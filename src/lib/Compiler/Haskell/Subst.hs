{-# LANGUAGE MultiParamTypeClasses #-}

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
  , singleSubst'
  , composeSubst
  , composeSubsts
    -- * Application
  , ApplySubst(..)
    -- * Rename arguments
  , renameTypeArgsSubst
  , renameTypeArgsSubst'
  , renameArgsSubst
  , renameArgs
  )
where

import           Data.Composition               ( (.:) )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromMaybe )

import           Compiler.Environment
import           Compiler.Environment.Fresh
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-- | A substitution is a mapping from Haskell variable names to expressions
--   (i.e. @'Subst' 'HS.Expr'@) or type expressions (i.e. @'Subst' 'HS.Type'@).
--
--   When the substitution is applied (see 'applySubst') the source span of
--   the substituted variable can be inserted into the (type) expression it is
--   replaced by (e.g. to rename a variable without loosing source spans).
--
--   The substitution contains 'Converter's because 'composeSubst' needs to
--   apply the first substitution on the elements of the second substitution,
--   but 'applySubst' is a 'Converter' (because it needs to generate fresh
--   identifiers).
newtype Subst a = Subst (Map HS.QName (SrcSpan -> Converter a))

-- | Substitutions can be pretty printed for testing purposes.
instance Pretty a => Pretty (Subst a) where
  pretty (Subst m) =
    braces
      $ prettySeparated (comma <> space)
      $ fromMaybe []
      $ evalReporter
      $ flip evalConverter emptyEnv
      $ flip mapM          (Map.assocs m)
      $ \(v, f) -> do
          x <- f NoSrcSpan
          return (pretty v <+> prettyString "->" <+> pretty x)

-------------------------------------------------------------------------------
-- Construction                                                              --
-------------------------------------------------------------------------------

-- | A substitution that does not change an expression.
identitySubst :: Subst a
identitySubst = Subst Map.empty

-- | Creates a new substitution that maps the variable with the given name
--   to the given expression or type expression.
singleSubst :: HS.QName -> a -> Subst a
singleSubst = flip (flip singleSubst' . const)

-- | Like 'singleSubst', but can be used to preserve the source span of the
--   variable replaced by 'applySubst'.
--
--   For internal use only.
singleSubst' :: HS.QName -> (SrcSpan -> a) -> Subst a
singleSubst' = flip (flip singleSubst'' . (return .))

-- | Like 'singleSubst'', but the generated expression can access the
--   environment and report errors.
--
--   For internal use only.
singleSubst'' :: HS.QName -> (SrcSpan -> Converter a) -> Subst a
singleSubst'' = Subst .: Map.singleton

-- | Creates a new substituion that applies both given substitutions after
--   each other.
composeSubst :: ApplySubst a a => Subst a -> Subst a -> Subst a
composeSubst s2@(Subst m2) (Subst m1) =
  let m1' = fmap (\f srcSpan -> f srcSpan >>= applySubst s2) m1
      m2' = Map.filterWithKey (const . (`Map.notMember` m1)) m2
  in  Subst (m2' `Map.union` m1')

-- | Creates a new substituion that applies all given substitutions after
--   each other.
composeSubsts :: ApplySubst a a => [Subst a] -> Subst a
composeSubsts = foldl composeSubst identitySubst

-------------------------------------------------------------------------------
-- Application of substitutions                                              --
-------------------------------------------------------------------------------

-- | Type class for applying a substitution that replaces variables by
--   values of type @a@ on values of type @b@.
class ApplySubst a b where
  applySubst :: Subst a -> b -> Converter b

-------------------------------------------------------------------------------
-- Application to expressions                                                --
-------------------------------------------------------------------------------

-- | Applies the given expression substitution to an expression.
--
--   This function uses the 'Converter' monad, because we need to create fresh
--   identifiers. This is because we have to rename arguments of lambda
--   abstractions and @case@-alternatives, such that no name conflict can
--   occur.
instance ApplySubst HS.Expr HS.Expr where
  applySubst subst@(Subst substMap) = applySubst'
   where
    applySubst' :: HS.Expr -> Converter HS.Expr
    applySubst' var@(HS.Var srcSpan name) =
      maybe (return var) ($ srcSpan) (Map.lookup name substMap)

    -- Substitute recursively.
    applySubst' (HS.App srcSpan e1 e2) = do
      e1' <- applySubst' e1
      e2' <- applySubst' e2
      return (HS.App srcSpan e1' e2')
    applySubst' (HS.TypeAppExpr srcSpan expr typeExpr) = do
      expr' <- applySubst' expr
      return (HS.TypeAppExpr srcSpan expr' typeExpr)
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
    applySubst' (HS.ExprTypeSig srcSpan expr typeSchema) = do
      expr' <- applySubst' expr
      return (HS.ExprTypeSig srcSpan expr' typeSchema)

    -- All other expressions remain unchanged.
    applySubst' expr@(HS.Con _ _       ) = return expr
    applySubst' expr@(HS.Undefined _   ) = return expr
    applySubst' expr@(HS.ErrorExpr  _ _) = return expr
    applySubst' expr@(HS.IntLiteral _ _) = return expr

    -- | Applies the substituion on the current substitution.
    applySubstAlt :: HS.Alt -> Converter HS.Alt
    applySubstAlt (HS.Alt srcSpan conPat varPats expr) = do
      (varPats', varPatSubst) <- renameArgsSubst varPats
      expr' <- applySubst (composeSubst subst varPatSubst) expr
      return (HS.Alt srcSpan conPat varPats' expr')

-- | Applies the given type substitution to an expression.
instance ApplySubst HS.Type HS.Expr where
  applySubst subst = applySubst'
   where
    applySubst' :: HS.Expr -> Converter HS.Expr
    applySubst' (HS.App srcSpan e1 e2) = do
      e1' <- applySubst' e1
      e2' <- applySubst' e2
      return (HS.App srcSpan e1' e2')
    applySubst' (HS.TypeAppExpr srcSpan expr typeExpr) = do
      expr' <- applySubst' expr
      typeExpr' <- applySubst subst typeExpr
      return (HS.TypeAppExpr srcSpan expr' typeExpr')
    applySubst' (HS.If srcSpan e1 e2 e3) = do
      e1' <- applySubst' e1
      e2' <- applySubst' e2
      e3' <- applySubst' e3
      return (HS.If srcSpan e1' e2' e3')
    applySubst' (HS.Case srcSpan expr alts) = do
      expr' <- applySubst' expr
      return (HS.Case srcSpan expr' alts)
    applySubst' (HS.Lambda srcSpan args expr) = do
      expr' <- applySubst' expr
      return (HS.Lambda srcSpan args expr')
    applySubst' (HS.ExprTypeSig srcSpan expr typeSchema) = do
      expr' <- applySubst' expr
      typeSchema' <- applySubst subst typeSchema
      return (HS.ExprTypeSig srcSpan expr' typeSchema')

    -- All other expressions remain unchanged.
    applySubst' expr@(HS.Var _ _) = return expr
    applySubst' expr@(HS.Con _ _       ) = return expr
    applySubst' expr@(HS.Undefined _   ) = return expr
    applySubst' expr@(HS.ErrorExpr  _ _) = return expr
    applySubst' expr@(HS.IntLiteral _ _) = return expr

-------------------------------------------------------------------------------
-- Application to function declarations.                                     --
-------------------------------------------------------------------------------

-- | Applies the given expression substitution to the right-hand side of a
--   function declaration.
instance ApplySubst HS.Expr HS.FuncDecl where
  applySubst subst (HS.FuncDecl srcSpan declIdent args rhs) = do
    (args', argSubst) <- renameArgsSubst args
    rhs'              <- applySubst (composeSubst subst argSubst) rhs
    return (HS.FuncDecl srcSpan declIdent args' rhs')

-- | Applies the given type substitution to the right-hand side of a
--   function declaration.
instance ApplySubst HS.Type HS.FuncDecl where
  applySubst subst (HS.FuncDecl srcSpan declIdent args rhs) = do
    rhs' <- applySubst subst rhs
    return (HS.FuncDecl srcSpan declIdent args rhs')

-------------------------------------------------------------------------------
-- Application to type expressions                                           --
-------------------------------------------------------------------------------

-- | Applies the given type substitution to a type expression.
instance ApplySubst HS.Type HS.Type where
  applySubst (Subst substMap) = applySubst'
   where
    applySubst' :: HS.Type -> Converter HS.Type
    applySubst' typeCon@(HS.TypeCon _ _) = return typeCon
    applySubst' typeVar@(HS.TypeVar srcSpan ident) = maybe
      (return typeVar)
      ($ srcSpan)
      (Map.lookup (HS.UnQual (HS.Ident ident)) substMap)
    applySubst' (HS.TypeApp srcSpan t1 t2) = do
      t1' <- applySubst' t1
      t2' <- applySubst' t2
      return (HS.TypeApp srcSpan t1' t2')
    applySubst' (HS.TypeFunc srcSpan t1 t2) = do
      t1' <- applySubst' t1
      t2' <- applySubst' t2
      return (HS.TypeFunc srcSpan t1' t2')

-------------------------------------------------------------------------------
-- Application to type schemas                                           --
-------------------------------------------------------------------------------

-- | Applies the given type substitution to a type schema.
instance ApplySubst HS.Type HS.TypeSchema where
  applySubst subst (HS.TypeSchema srcSpan typeArgs typeExpr) = do
    let typeArgIdents     = map HS.fromDeclIdent typeArgs
        declIdentSrcSpans = map HS.getSrcSpan typeArgs
    (typeArgSubst, typeArgsIdents') <- renameTypeArgsSubst' typeArgIdents
    let subst'    = composeSubst subst typeArgSubst
        typeArgs' = zipWith HS.DeclIdent declIdentSrcSpans typeArgsIdents'
    typeExpr' <- applySubst subst' typeExpr
    return (HS.TypeSchema srcSpan typeArgs' typeExpr')

-------------------------------------------------------------------------------
-- Rename arguments                                                          --
-------------------------------------------------------------------------------

-- | Creates a substitution that renames the given type variables to fresh
--   variables.
renameTypeArgsSubst :: [HS.TypeVarIdent] -> Converter (Subst HS.Type)
renameTypeArgsSubst = fmap fst . renameTypeArgsSubst'

-- | Like 'renameTypeArgsSubst' but also returns the new type variables.
renameTypeArgsSubst'
  :: [HS.TypeVarIdent] -> Converter (Subst HS.Type, [HS.TypeVarIdent])
renameTypeArgsSubst' typeArgIdents = do
  typeArgIdents' <- mapM freshHaskellIdent typeArgIdents
  let typeArgs'    = map (HS.TypeVar NoSrcSpan) typeArgIdents'
      typeArgNames = map (HS.UnQual . HS.Ident) typeArgIdents
      subst        = composeSubsts (zipWith singleSubst typeArgNames typeArgs')
  return (subst, typeArgIdents')

-- | Creates a substitution that renames the arguments bound by the given
--   variable patterns to fresh variables.
--
--   Returns the new names for the variables and the substitution.
renameArgsSubst :: [HS.VarPat] -> Converter ([HS.VarPat], Subst HS.Expr)
renameArgsSubst args = do
  args' <- mapM freshVarPat args
  let argNames = map (HS.UnQual . HS.Ident . HS.fromVarPat) args
      argVars' = map (flip HS.Var . HS.UnQual . HS.Ident . HS.fromVarPat) args'
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
