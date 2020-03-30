{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances
           , FunctionalDependencies, AllowAmbiguousTypes #-}

-- | This module contains a definition of substitutions for expressions and
--   type expressions.

module Compiler.IR.Subst
  ( -- * Substitutions
    Subst
    -- * Construction
  , identitySubst
  , singleSubst
  , singleSubst'
  -- * Composition
  , composeSubst
  , composeSubsts
  -- * Modification
  , filterSubst
  , substWithout
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
import           Data.Maybe                     ( mapMaybe )
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set

import           Compiler.Environment.Fresh
import           Compiler.Environment.Scope
import           Compiler.IR.Reference
import           Compiler.IR.SrcSpan
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Monad.Converter
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Substitutions                                                             --
-------------------------------------------------------------------------------

-- | A substitution is a mapping from Haskell variable names to expressions
--   (i.e. @'Subst' 'HS.Expr'@) or type expressions (i.e. @'Subst' 'HS.Type'@).
--
--   When the substitution is applied (see 'applySubst') the source span of
--   the substituted variable can be inserted into the (type) expression it is
--   replaced by (e.g. to rename a variable without loosing source spans).
newtype Subst a = Subst (Map HS.QName (SrcSpan -> a))

-- | Substitutions can be pretty printed for testing purposes.
instance Pretty a => Pretty (Subst a) where
  pretty (Subst m) =
    braces
      $ prettySeparated (comma <> space)
      $ flip map (Map.assocs m)
      $ \(v, f) -> pretty v <+> prettyString "↦" <+> pretty (f NoSrcSpan)

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
singleSubst' :: HS.QName -> (SrcSpan -> a) -> Subst a
singleSubst' = Subst .: Map.singleton

-------------------------------------------------------------------------------
-- Composition                                                               --
-------------------------------------------------------------------------------

-- | Creates a new substitution that applies both given substitutions after
--   each other.
composeSubst :: ApplySubst a a => Subst a -> Subst a -> Subst a
composeSubst s2@(Subst m2) (Subst m1) =
  let m1' = fmap (\f srcSpan -> applySubst s2 (f srcSpan)) m1
      m2' = Map.filterWithKey (const . (`Map.notMember` m1)) m2
  in  Subst (m2' `Map.union` m1')

-- | Creates a new substitution that applies all given substitutions after
--   each other.
composeSubsts :: ApplySubst a a => [Subst a] -> Subst a
composeSubsts = foldl composeSubst identitySubst

-------------------------------------------------------------------------------
-- Modification                                                              --
-------------------------------------------------------------------------------

-- | Creates a new substitution whose domain does not contain the names
--   that match the given predicate.
filterSubst :: (HS.QName -> Bool) -> Subst a -> Subst a
filterSubst p (Subst m) = Subst (Map.filterWithKey (const . p) m)

-- | Creates a new substitution whose domain does not contain the given names.
substWithout :: Subst a -> [HS.QName] -> Subst a
substWithout subst names = filterSubst (`notElem` names) subst

-------------------------------------------------------------------------------
-- Application of substitutions                                              --
-------------------------------------------------------------------------------

-- | Type class for applying a substitution that replaces variables by
--   values of type @a@ on values of type @b@.
class ApplySubst a b where
  applySubst :: Subst a -> b -> b

-- | Substitutions can be applied to the elements of every functor.
instance (ApplySubst a b, Functor f) => ApplySubst a (f b) where
  applySubst = fmap . applySubst

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
    applySubst' :: HS.Expr -> HS.Expr
    applySubst' var@(HS.Var srcSpan name _) =
      maybe var ($ srcSpan) (Map.lookup name substMap)

    -- Substitute recursively.
    applySubst' (HS.App srcSpan e1 e2 exprType) =
      let e1' = applySubst' e1
          e2' = applySubst' e2
      in  HS.App srcSpan e1' e2' exprType
    applySubst' (HS.TypeAppExpr srcSpan expr typeExpr exprType) =
      let expr' = applySubst' expr
      in  HS.TypeAppExpr srcSpan expr' typeExpr exprType
    applySubst' (HS.If srcSpan e1 e2 e3 exprType) =
      let e1' = applySubst' e1
          e2' = applySubst' e2
          e3' = applySubst' e3
      in  HS.If srcSpan e1' e2' e3' exprType
    applySubst' (HS.Case srcSpan expr alts exprType) =
      let expr' = applySubst' expr
          alts' = map (applySubst subst) alts
      in  HS.Case srcSpan expr' alts' exprType
    applySubst' (HS.Lambda srcSpan args expr exprType) =
      let (subst', args') = newRenameArgs subst args
          expr'           = applySubst subst' expr
      in  HS.Lambda srcSpan args' expr' exprType

    -- All other expressions remain unchanged.
    applySubst' expr@(HS.Con _ _ _       ) = expr
    applySubst' expr@(HS.Undefined _ _   ) = expr
    applySubst' expr@(HS.ErrorExpr  _ _ _) = expr
    applySubst' expr@(HS.IntLiteral _ _ _) = expr

-- | Applies the given expression substitution to the right-hand side of the
--   given @case@-expression alterntaive.
instance ApplySubst HS.Expr HS.Alt where
  applySubst subst (HS.Alt srcSpan conPat varPats expr) =
    let (subst', varPats') = newRenameArgs subst varPats
        expr'              = applySubst subst' expr
    in  HS.Alt srcSpan conPat varPats' expr'

-------------------------------------------------------------------------------
-- Application to types in expressions                                       --
-------------------------------------------------------------------------------

-- | Applies the given type substitution to an expression.
instance ApplySubst HS.Type HS.Expr where
  applySubst subst = applySubst'
   where
    applySubst' :: HS.Expr -> HS.Expr

    applySubst' (HS.Con srcSpan conName exprType) =
      let exprType' = applySubst subst exprType
      in  HS.Con srcSpan conName exprType'

    applySubst' (HS.Var srcSpan varName exprType) =
      let exprType' = applySubst subst exprType
      in  HS.Var srcSpan varName exprType'

    applySubst' (HS.App srcSpan e1 e2 exprType) =
      let e1'       = applySubst' e1
          e2'       = applySubst' e2
          exprType' = applySubst subst exprType
      in  HS.App srcSpan e1' e2' exprType'

    applySubst' (HS.TypeAppExpr srcSpan expr typeExpr exprType) =
      let expr'     = applySubst' expr
          typeExpr' = applySubst subst typeExpr
          exprType' = applySubst subst exprType
      in  HS.TypeAppExpr srcSpan expr' typeExpr' exprType'

    applySubst' (HS.If srcSpan e1 e2 e3 exprType) =
      let e1'       = applySubst' e1
          e2'       = applySubst' e2
          e3'       = applySubst' e3
          exprType' = applySubst subst exprType
      in  HS.If srcSpan e1' e2' e3' exprType'

    applySubst' (HS.Case srcSpan expr alts exprType) =
      let expr'     = applySubst' expr
          alts'     = applySubst subst alts
          exprType' = applySubst subst exprType
      in  HS.Case srcSpan expr' alts' exprType'

    applySubst' (HS.Undefined srcSpan exprType) =
      let exprType' = applySubst subst exprType
      in  HS.Undefined srcSpan exprType'

    applySubst' (HS.ErrorExpr srcSpan msg exprType) =
      let exprType' = applySubst subst exprType
      in  HS.ErrorExpr srcSpan msg exprType'

    applySubst' (HS.IntLiteral srcSpan value exprType) =
      let exprType' = applySubst subst exprType
      in  HS.IntLiteral srcSpan value exprType'

    applySubst' (HS.Lambda srcSpan args expr exprType) =
      let args'     = applySubst subst args
          expr'     = applySubst' expr
          exprType' = applySubst subst exprType
      in  HS.Lambda srcSpan args' expr' exprType'

-- | Applies the given type substitution to the right-hand side of the
--   given @case@-expression alterntaive.
instance ApplySubst HS.Type HS.Alt where
  applySubst subst (HS.Alt srcSpan conPat varPats expr) =
    let varPats' = applySubst subst varPats
        expr'    = applySubst subst expr
    in  HS.Alt srcSpan conPat varPats' expr'

-- | Applies the given type substitution to the type annotation of the given
--   variable pattern.
instance ApplySubst HS.Type HS.VarPat where
  applySubst subst (HS.VarPat srcSpan varIdent maybeVarType) =
    let maybeVarType' = applySubst subst maybeVarType
    in  HS.VarPat srcSpan varIdent maybeVarType'

-------------------------------------------------------------------------------
-- Application to function declarations.                                     --
-------------------------------------------------------------------------------

-- | Applies the given expression substitution to the right-hand side of a
--   function declaration.
instance ApplySubst HS.Expr HS.FuncDecl where
  applySubst subst (HS.FuncDecl srcSpan declIdent typeArgs args rhs maybeRetType)
    = let (subst', args') = newRenameArgs subst args
          rhs'            = applySubst subst' rhs
      in  HS.FuncDecl srcSpan declIdent typeArgs args' rhs' maybeRetType

-- | Applies the given type substitution to the right-hand side of a
--   function declaration.
instance ApplySubst HS.Type HS.FuncDecl where
  applySubst subst (HS.FuncDecl srcSpan declIdent typeArgs args rhs maybeRetType)
    = let args'         = applySubst subst args
          rhs'          = applySubst subst rhs
          maybeRetType' = applySubst subst maybeRetType
      in  HS.FuncDecl srcSpan declIdent typeArgs args' rhs' maybeRetType'

-------------------------------------------------------------------------------
-- Application to type expressions                                           --
-------------------------------------------------------------------------------

-- | Applies the given type substitution to a type expression.
instance ApplySubst HS.Type HS.Type where
  applySubst (Subst substMap) = applySubst'
   where
    applySubst' :: HS.Type -> HS.Type
    applySubst' typeCon@(HS.TypeCon _       _    ) = typeCon
    applySubst' typeVar@(HS.TypeVar srcSpan ident) = maybe
      typeVar
      ($ srcSpan)
      (Map.lookup (HS.UnQual (HS.Ident ident)) substMap)
    applySubst' (HS.TypeApp srcSpan t1 t2) =
      let t1' = applySubst' t1
          t2' = applySubst' t2
      in  HS.TypeApp srcSpan t1' t2'
    applySubst' (HS.FuncType srcSpan t1 t2) =
      let t1' = applySubst' t1
          t2' = applySubst' t2
      in  HS.FuncType srcSpan t1' t2'

-------------------------------------------------------------------------------
-- Application to type schemas                                           --
-------------------------------------------------------------------------------

-- | Applies the given type substitution to a type schema.
instance ApplySubst HS.Type HS.TypeSchema where
  applySubst subst (HS.TypeSchema srcSpan typeArgs typeExpr) =
    let (subst', typeArgs') = newRenameArgs subst typeArgs
        typeExpr'           = applySubst subst' typeExpr
    in  HS.TypeSchema srcSpan typeArgs' typeExpr'

-------------------------------------------------------------------------------
-- Renaming arguments                                                        --
-------------------------------------------------------------------------------

-- | Type class for (type) arguments of type @arg@ that can be renamed in
--   (type) expressions of type @expr@.
class Renamable arg expr | arg -> expr, expr -> arg where
  -- | Gets the identifier that is bound by the given argument.
  getIdent :: arg -> String

  -- | Updates the identifier that is bound by the given argument.
  setIdent :: arg -> String -> arg

  -- | Gets the scope the given argument declares an identifier in.
  getScope :: arg -> Scope

  -- | Converts the given argument to an expression that refers to
  --   the argument.
  toExpr :: arg -> SrcSpan -> expr

-- | Type variable declarations bind type variables in type expressions and
--   can be renamed.
instance Renamable HS.TypeVarDecl HS.Type where
  getIdent = HS.typeVarDeclIdent
  setIdent typeArg ident' = typeArg { HS.typeVarDeclIdent = ident' }
  getScope = const TypeScope
  toExpr   = flip HS.TypeVar . getIdent

-- | Variable patterns bind variables in expressions and can be renamed.
instance Renamable HS.VarPat HS.Expr where
  getIdent = HS.varPatIdent
  setIdent varPat ident' = varPat { HS.varPatIdent = ident' }
  getScope = const ValueScope
  toExpr   = flip HS.untypedVar . HS.UnQual . HS.Ident . getIdent

-- | Renames the given (type) arguments such that there are no name conflicts
--   with the given substitution.
--
--   Returns the renamed (type) arguments as well as a modified substitution
--   that replaces the renamed (type) arguments appropriately.
newRenameArgs
  :: (HasRefs expr, Renamable arg expr, ApplySubst expr expr)
  => Subst expr
  -> [arg]
  -> (Subst expr, [arg])
newRenameArgs subst args =
  let subst' = subst `substWithout` map (HS.UnQual . HS.Ident . getIdent) args
  in  newRenameArgs' subst' args

-- | Like 'newRenameArgs' but the domain of the given substitution does not
--   contain any of the given type arguments.
newRenameArgs'
  :: (HasRefs expr, Renamable arg expr, ApplySubst expr expr)
  => Subst expr
  -> [arg]
  -> (Subst expr, [arg])
newRenameArgs' subst []           = (subst, [])
newRenameArgs' subst (arg : args) = (arg' :) <$> newRenameArgs' subst' args
 where
  -- | The original identifier of the argument.
  argIdent :: String
  argIdent = getIdent arg

  -- | The unqualified original name of the argument.
  argName :: HS.QName
  argName = HS.UnQual (HS.Ident argIdent)

  -- | The new identifier of the argument.
  --
  --   This is the first identifier that is prefixed with the original
  --   identifier and does not occur freely in the substitution.
  argIdent' :: String
  argIdent' = head (filter isNotFree (freshIdentsWithPrefix argIdent))

  -- | Tests whether the given identifier does not occur freely in
  --   the substitution.
  isNotFree :: String -> Bool
  isNotFree = flip Set.notMember (freeSubstIdents (getScope arg) subst)

  -- | Before the actual substitution is applied, all occurrences of the
  --   original (type) variable must be replaced by the renamed (type) variable.
  {- subst' :: Subst expr -}
  subst'    = subst `composeSubst` singleSubst' argName (toExpr arg')

  -- | The renamed argument.
  {- arg' :: arg -}
  arg'      = setIdent arg argIdent'

-- | Gets the identifiers that occur freely on in the specified scope of the
--   given substitution.
freeSubstIdents :: HasRefs a => Scope -> Subst a -> Set String
freeSubstIdents scope (Subst substMap) =
  Set.fromList
    $ mapMaybe (HS.identFromQName . refName)
    $ filter ((== scope) . refScope)
    $ concatMap (refs . ($ NoSrcSpan))
    $ Map.elems substMap

-- | Generates identifiers that start with the given prefix and can be used as
--   fresh identifiers.
--
--   Returns the identifier that equals the prefix as well as each identifier
--   that starts with the prefix followed by an increasing number starting with
--   zero.
freshIdentsWithPrefix :: String -> [String]
freshIdentsWithPrefix prefix = map (prefix ++) ("" : map show [0 :: Int ..])

-------------------------------------------------------------------------------
-- Rename arguments (old)                                                    --
-------------------------------------------------------------------------------

-- | Creates a substitution that renames the given type variables to fresh
--   variables.
--
--   Returns the new names for the type variables and the substitution.
renameTypeArgsSubst
  :: [HS.TypeVarDecl] -> Converter ([HS.TypeVarDecl], Subst HS.Type)
renameTypeArgsSubst typeArgDecls = do
  typeArgDecls' <- mapM freshTypeArgDecl typeArgDecls
  let typeArgNames = map HS.typeVarDeclQName typeArgDecls
      typeArgs'    = map (flip HS.TypeVar . HS.typeVarDeclIdent) typeArgDecls'
      subst        = composeSubsts (zipWith singleSubst' typeArgNames typeArgs')
  return (typeArgDecls', subst)
 where
  -- | Generates a fresh identifier for the given type argument and returns
  --   a type argument that preserves the source span of the original
  --   declaration.
  freshTypeArgDecl :: HS.TypeVarDecl -> Converter HS.TypeVarDecl
  freshTypeArgDecl (HS.TypeVarDecl srcSpan ident) = do
    ident' <- freshHaskellIdent ident
    return (HS.TypeVarDecl srcSpan ident')

-- | Renames the given type variables in the given expression or type
--   to fresh type variables.
renameTypeArgs
  :: ApplySubst HS.Type a
  => [HS.TypeVarDecl]
  -> a
  -> Converter ([HS.TypeVarDecl], a)
renameTypeArgs typeArgDecls x = do
  (typeArgDecls', subst) <- renameTypeArgsSubst typeArgDecls
  return (typeArgDecls', applySubst subst x)

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
  return (args', applySubst subst x)
