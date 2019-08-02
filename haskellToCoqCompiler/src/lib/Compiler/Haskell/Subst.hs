-- | This module contains a definition of substitutions for Haskell
--   expressions.
--
--   Substitutions are used by "Compiler.Haskell.Inliner" to replace
--   parameters of inlined functions with their actual arguments.

module Compiler.Haskell.Subst
  ( Subst
    -- * Construction
  , identitySubst
  , singleSubst
  , composeSubst
  , composeSubsts
    -- * Application
  , applySubst
    -- * Rename arguments
  , renameArgsSubst
  , renameArgs
  )
where

import           Data.Composition               ( (.:) )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map


import           Compiler.Environment.Fresh
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter

-- | A substitution is a mapping from Haskell variable names to expressions.
--
--   When the substitution is applied (see 'applySubst') the source span of
--   the substituted variable can be inserted into the expression it is
--   replaced by (e.g. to rename a variable without loosing source spans).
--
--   The substitution contains 'Converter's because 'composeSubst' needs to
--   apply the first substitution on the elements of the second substitution,
--   but `applySubst` is a `Converter` (because it need to generate fresh
--   identifiers).
newtype Subst = Subst (Map HS.Name (SrcSpan -> Converter HS.Expr))

-------------------------------------------------------------------------------
-- Construction                                                              --
-------------------------------------------------------------------------------

-- | A substitution that does not change an expression.
identitySubst :: Subst
identitySubst = Subst Map.empty

-- | Creates a new substitution that maps the variable with the given name
--   to the given expression.
singleSubst :: HS.Name -> HS.Expr -> Subst
singleSubst = flip (flip singleSubst' . const)

-- | Like 'singleSubst', but can be used to preserve the source span of the
--   variable replaced by 'applySubst'.
--
--   For internal use only.
singleSubst' :: HS.Name -> (SrcSpan -> HS.Expr) -> Subst
singleSubst' = flip (flip singleSubst'' . (return .))

-- | Like 'singleSubst'', but the generated expression can access the
--   environment and report errors.
--
--   For internal use only.
singleSubst'' :: HS.Name -> (SrcSpan -> Converter HS.Expr) -> Subst
singleSubst'' = Subst .: Map.singleton

-- | Creates a new substituion that applies both given substitutions after
--   each other.
composeSubst :: Subst -> Subst -> Subst
composeSubst s1@(Subst m1) (Subst m2) =
  let m2' = fmap (\f srcSpan -> f srcSpan >>= applySubst s1) m2
  in  Subst (m1 `Map.union` m2')

-- | Creates a new substituion that applies all given substitutions after
--   each other.
composeSubsts :: [Subst] -> Subst
composeSubsts = foldl composeSubst identitySubst

-------------------------------------------------------------------------------
-- Application                                                               --
-------------------------------------------------------------------------------

-- | Applies the given substitution to an expression.
--
--   This function uses the @Converter@ monad, because we need to create fresh
--   identifiers. This is because we have to rename arguments of lambda
--   abstractions and @case@-alternatives, such that no name conflict can
--   occur.
applySubst :: Subst -> HS.Expr -> Converter HS.Expr
applySubst subst@(Subst substMap) = applySubst'
 where
  applySubst' :: HS.Expr -> Converter HS.Expr
  applySubst' expr@(HS.Var srcSpan name) =
    maybe (return expr) ($ srcSpan) (Map.lookup name substMap)

  -- Substitute recursively.
  applySubst' (HS.App srcSpan e1 e2) = do
    e1' <- applySubst' e1
    e2' <- applySubst' e2
    return (HS.App srcSpan e1' e2')
  applySubst' (HS.If srcSpan e1 e2 e3) = do
    e1' <- applySubst' e1
    e2' <- applySubst' e2
    e3' <- applySubst' e3
    return (HS.If srcSpan e1' e2' e3')
  applySubst' (HS.Case srcSpan expr alts) = do
    expr' <- applySubst' expr
    alts' <- mapM applySubstAlt alts
    return (HS.Case srcSpan expr' alts')
  applySubst' (HS.Lambda srcSpan args expr) = do
    (args', argSubst) <- renameArgsSubst args
    expr'             <- applySubst (composeSubst subst argSubst) expr
    return (HS.Lambda srcSpan args' expr')

  -- All other expressions remain unchanged.
  applySubst' expr@(HS.Con _ _       ) = return expr
  applySubst' expr@(HS.Undefined _   ) = return expr
  applySubst' expr@(HS.ErrorExpr  _ _) = return expr
  applySubst' expr@(HS.IntLiteral _ _) = return expr

  -- | Applies the substituion on the current substitution.
  applySubstAlt :: HS.Alt -> Converter HS.Alt
  applySubstAlt (HS.Alt srcSpan conPat varPats expr) = do
    (varPats', varPatSubst) <- renameArgsSubst varPats
    expr'                   <- applySubst (composeSubst subst varPatSubst) expr
    return (HS.Alt srcSpan conPat varPats' expr')

-------------------------------------------------------------------------------
-- Rename arguments                                                          --
-------------------------------------------------------------------------------

-- | Creates a substitution that renames the arguments bound by the given
--   variable patterns to fresh variables.
--
--   Returns the new names for the variables and the substitution.
renameArgsSubst :: [HS.VarPat] -> Converter ([HS.VarPat], Subst)
renameArgsSubst args = do
  args' <- mapM freshVarPat args
  let argNames = map (HS.Ident . HS.fromVarPat) args
      argVars' = map (flip HS.Var . HS.Ident . HS.fromVarPat) args'
      argSubst = composeSubsts (zipWith singleSubst' argNames argVars')
  return (args', argSubst)
 where
  -- | Generates a fresh identifier for the given variable pattern and returns
  --   a variable pattern that preserves the source span of the original
  --   pattern.
  freshVarPat :: HS.VarPat -> Converter HS.VarPat
  freshVarPat (HS.VarPat srcSpan ident) = do
    ident' <- freshHaskellIdent ident
    return (HS.VarPat srcSpan ident')

-- | Renames the arguments bound by the given variable patterns in the given
--   expression to fresh variables.
--
--   Returns the new names for the variables and the resulting expression.
renameArgs :: [HS.VarPat] -> HS.Expr -> Converter ([HS.VarPat], HS.Expr)
renameArgs args expr = do
  (args', subst) <- renameArgsSubst args
  expr'          <- applySubst subst expr
  return (args', expr')
