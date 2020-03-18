{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}

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
  , renameTypeArgs
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
          return (pretty v <+> prettyString "↦" <+> pretty x)

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
    applySubst' var@(HS.Var srcSpan name _) =
      maybe (return var) ($ srcSpan) (Map.lookup name substMap)

    -- Substitute recursively.
    applySubst' (HS.App srcSpan e1 e2 exprType) = do
      e1' <- applySubst' e1
      e2' <- applySubst' e2
      return (HS.App srcSpan e1' e2' exprType)
    applySubst' (HS.TypeAppExpr srcSpan expr typeExpr exprType) = do
      expr' <- applySubst' expr
      return (HS.TypeAppExpr srcSpan expr' typeExpr exprType)
    applySubst' (HS.If srcSpan e1 e2 e3 exprType) = do
      e1' <- applySubst' e1
      e2' <- applySubst' e2
      e3' <- applySubst' e3
      return (HS.If srcSpan e1' e2' e3' exprType)
    applySubst' (HS.Case srcSpan expr alts exprType) = do
      expr' <- applySubst' expr
      alts' <- mapM (applySubst subst) alts
      return (HS.Case srcSpan expr' alts' exprType)
    applySubst' (HS.Lambda srcSpan args expr exprType) = do
      (args', argSubst) <- renameArgsSubst args
      expr'             <- applySubst (composeSubst subst argSubst) expr
      return (HS.Lambda srcSpan args' expr' exprType)
    applySubst' (HS.ExprTypeSig srcSpan expr typeSchema exprType) = do
      expr' <- applySubst' expr
      return (HS.ExprTypeSig srcSpan expr' typeSchema exprType)

    -- All other expressions remain unchanged.
    applySubst' expr@(HS.Con _ _ _       ) = return expr
    applySubst' expr@(HS.Undefined _ _   ) = return expr
    applySubst' expr@(HS.ErrorExpr  _ _ _) = return expr
    applySubst' expr@(HS.IntLiteral _ _ _) = return expr

-- | Applies the given expression substitution to the right-hand side of the
--   given @case@-expression alterntaive.
instance ApplySubst HS.Expr HS.Alt where
  applySubst subst (HS.Alt srcSpan conPat varPats expr) = do
    (varPats', varPatSubst) <- renameArgsSubst varPats
    expr' <- applySubst (composeSubst subst varPatSubst) expr
    return (HS.Alt srcSpan conPat varPats' expr')

-- | Applies the given type substitution to an expression.
instance ApplySubst HS.Type HS.Expr where
  applySubst subst = applySubst'
   where
    applySubst' :: HS.Expr -> Converter HS.Expr

    applySubst' (HS.Con srcSpan conName exprType) = do
      exprType' <- mapM (applySubst subst) exprType
      return (HS.Con srcSpan conName exprType')

    applySubst' (HS.Var srcSpan varName exprType) = do
      exprType' <- mapM (applySubst subst) exprType
      return (HS.Var srcSpan varName exprType')

    applySubst' (HS.App srcSpan e1 e2 exprType) = do
      e1' <- applySubst' e1
      e2' <- applySubst' e2
      exprType' <- mapM (applySubst subst) exprType
      return (HS.App srcSpan e1' e2' exprType')

    applySubst' (HS.TypeAppExpr srcSpan expr typeExpr exprType) = do
      expr'     <- applySubst' expr
      typeExpr' <- applySubst subst typeExpr
      exprType' <- mapM (applySubst subst) exprType
      return (HS.TypeAppExpr srcSpan expr' typeExpr' exprType')

    applySubst' (HS.If srcSpan e1 e2 e3 exprType) = do
      e1' <- applySubst' e1
      e2' <- applySubst' e2
      e3' <- applySubst' e3
      exprType' <- mapM (applySubst subst) exprType
      return (HS.If srcSpan e1' e2' e3' exprType')

    applySubst' (HS.Case srcSpan expr alts exprType) = do
      expr' <- applySubst' expr
      alts' <- mapM (applySubst subst) alts
      exprType' <- mapM (applySubst subst) exprType
      return (HS.Case srcSpan expr' alts' exprType')

    applySubst' (HS.Undefined srcSpan  exprType ) = do
      exprType' <- mapM (applySubst subst) exprType
      return (HS.Undefined srcSpan exprType')

    applySubst' (HS.ErrorExpr srcSpan msg exprType) = do
      exprType' <- mapM (applySubst subst) exprType
      return (HS.ErrorExpr  srcSpan msg exprType')

    applySubst' (HS.IntLiteral srcSpan value exprType) = do
      exprType' <- mapM (applySubst subst) exprType
      return (HS.IntLiteral srcSpan value exprType')

    applySubst' (HS.Lambda srcSpan args expr exprType) = do
      args' <- mapM (applySubst subst) args
      expr' <- applySubst' expr
      exprType' <- mapM (applySubst subst) exprType
      return (HS.Lambda srcSpan args' expr' exprType')

    applySubst' (HS.ExprTypeSig srcSpan expr typeSchema exprType) = do
      expr'       <- applySubst' expr
      typeSchema' <- applySubst subst typeSchema
      exprType' <- mapM (applySubst subst) exprType
      return (HS.ExprTypeSig srcSpan expr' typeSchema' exprType')

-- | Applies the given type substitution to the right-hand side of the
--   given @case@-expression alterntaive.
instance ApplySubst HS.Type HS.Alt where
  applySubst subst (HS.Alt srcSpan conPat varPats expr) = do
    varPats' <- mapM (applySubst subst) varPats
    expr'    <- applySubst subst expr
    return (HS.Alt srcSpan conPat varPats' expr')

-- | Applies the given type substitution to the type annotation of the given
--   variable pattern.
instance ApplySubst HS.Type HS.VarPat where
  applySubst subst (HS.VarPat srcSpan varIdent maybeVarType) = do
    maybeVarType' <- mapM (applySubst subst) maybeVarType
    return (HS.VarPat srcSpan varIdent maybeVarType')

-------------------------------------------------------------------------------
-- Application to function declarations.                                     --
-------------------------------------------------------------------------------

-- | Applies the given expression substitution to the right-hand side of a
--   function declaration.
instance ApplySubst HS.Expr HS.FuncDecl where
  applySubst subst (HS.FuncDecl srcSpan declIdent typeArgs args rhs maybeRetType) = do
    (args', argSubst) <- renameArgsSubst args
    rhs'              <- applySubst (composeSubst subst argSubst) rhs
    return (HS.FuncDecl srcSpan declIdent typeArgs args' rhs' maybeRetType)

-- | Applies the given type substitution to the right-hand side of a
--   function declaration.
instance ApplySubst HS.Type HS.FuncDecl where
  applySubst subst (HS.FuncDecl srcSpan declIdent typeArgs args rhs maybeRetType) = do
    args' <- mapM (applySubst subst) args
    rhs'  <- applySubst subst rhs
    maybeRetType' <- mapM (applySubst subst) maybeRetType
    return (HS.FuncDecl srcSpan declIdent typeArgs args' rhs' maybeRetType')

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
    applySubst' (HS.FuncType srcSpan t1 t2) = do
      t1' <- applySubst' t1
      t2' <- applySubst' t2
      return (HS.FuncType srcSpan t1' t2')

-------------------------------------------------------------------------------
-- Application to type schemas                                           --
-------------------------------------------------------------------------------

-- | Applies the given type substitution to a type schema.
instance ApplySubst HS.Type HS.TypeSchema where
  applySubst subst (HS.TypeSchema srcSpan typeArgs typeExpr) = do
    (typeArgs', typeArgSubst) <- renameTypeArgsSubst typeArgs
    let subst' = composeSubst subst typeArgSubst
    typeExpr' <- applySubst subst' typeExpr
    return (HS.TypeSchema srcSpan typeArgs' typeExpr')

-------------------------------------------------------------------------------
-- Rename arguments                                                          --
-------------------------------------------------------------------------------

-- | Creates a substitution that renames the given type variables to fresh
--   variables.
--
--   Returns the new names for the type variables and the substitution.
renameTypeArgsSubst
  :: [HS.TypeVarDecl] -> Converter ([HS.TypeVarDecl], Subst HS.Type)
renameTypeArgsSubst typeArgDecls = do
  typeArgDecls' <- mapM freshTypeArgDecl typeArgDecls
  let typeArgNames = map (HS.UnQual . HS.Ident . HS.fromDeclIdent) typeArgDecls
      typeArgs'    = map (flip HS.TypeVar . HS.fromDeclIdent) typeArgDecls'
      subst        = composeSubsts (zipWith singleSubst' typeArgNames typeArgs')
  return (typeArgDecls', subst)
 where
  -- | Generates a fresh identifier for the given type argument and returns
  --   a type argument that preserves the source span of the original
  --   declaration.
  freshTypeArgDecl :: HS.DeclIdent -> Converter HS.DeclIdent
  freshTypeArgDecl (HS.DeclIdent srcSpan ident) = do
    ident' <- freshHaskellIdent ident
    return (HS.DeclIdent srcSpan ident')

-- | Renames the given type variables in the given expression or type
--   to fresh type variables.
renameTypeArgs
  :: ApplySubst HS.Type a
  => [HS.TypeVarDecl]
  -> a
  -> Converter ([HS.TypeVarDecl], a)
renameTypeArgs typeArgDecls x = do
  (typeArgDecls', subst) <- renameTypeArgsSubst typeArgDecls
  x'                     <- applySubst subst x
  return (typeArgDecls', x')

-- | Creates a substitution that renames the arguments bound by the given
--   variable patterns to fresh variables.
--
--   Returns the new names for the variables and the substitution.
renameArgsSubst :: [HS.VarPat] -> Converter ([HS.VarPat], Subst HS.Expr)
renameArgsSubst args = do
  args' <- mapM freshVarPat args
  let argNames = map HS.varPatQName args
      argVars' = map (flip HS.untypedVar . HS.varPatQName) args'
      argSubst = composeSubsts (zipWith singleSubst' argNames argVars')
  return (args', argSubst)
 where
  -- | Generates a fresh identifier for the given variable pattern and returns
  --   a variable pattern that preserves the source span of the original
  --   pattern.
  freshVarPat :: HS.VarPat -> Converter HS.VarPat
  freshVarPat (HS.VarPat srcSpan varIdent maybeVarType) = do
    varIdent' <- freshHaskellIdent varIdent
    return (HS.VarPat srcSpan varIdent' maybeVarType)

-- | Renames the arguments bound by the given variable patterns in the given
--   expression to fresh variables.
--
--   Returns the new names for the variables and the resulting expression.
renameArgs
  :: ApplySubst HS.Expr a => [HS.VarPat] -> a -> Converter ([HS.VarPat], a)
renameArgs args x = do
  (args', subst) <- renameArgsSubst args
  x'             <- applySubst subst x
  return (args', x')
