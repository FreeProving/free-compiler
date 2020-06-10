{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies #-}

-- | This module contains a definition of substitutions for expressions and
--   type expressions.

module FreeC.IR.Subst
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

import           FreeC.Environment.Fresh
import           FreeC.IR.Reference
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Substitutions                                                             --
-------------------------------------------------------------------------------

-- | A substitution is a mapping from Haskell variable names to expressions
--   (i.e. @'Subst' 'IR.Expr'@) or type expressions (i.e. @'Subst' 'IR.Type'@).
--
--   When the substitution is applied (see 'applySubst') the source span of
--   the substituted variable can be inserted into the (type) expression it is
--   replaced by (e.g. to rename a variable without loosing source spans).
newtype Subst a = Subst (Map IR.QName (SrcSpan -> a))

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
singleSubst :: IR.QName -> a -> Subst a
singleSubst = flip (flip singleSubst' . const)

-- | Like 'singleSubst', but can be used to preserve the source span of the
--   variable replaced by 'applySubst'.
singleSubst' :: IR.QName -> (SrcSpan -> a) -> Subst a
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
filterSubst :: (IR.QName -> Bool) -> Subst a -> Subst a
filterSubst p (Subst m) = Subst (Map.filterWithKey (const . p) m)

-- | Creates a new substitution whose domain does not contain the given names.
substWithout :: Subst a -> [IR.QName] -> Subst a
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
instance ApplySubst IR.Expr IR.Expr where
  applySubst subst@(Subst substMap) = applySubst'
   where
    applySubst' :: IR.Expr -> IR.Expr
    applySubst' var@(IR.Var srcSpan name _) =
      maybe var ($ srcSpan) (Map.lookup name substMap)

    -- Substitute recursively.
    applySubst' (IR.App srcSpan e1 e2 exprType) =
      let e1' = applySubst' e1
          e2' = applySubst' e2
      in  IR.App srcSpan e1' e2' exprType
    applySubst' (IR.TypeAppExpr srcSpan expr typeExpr exprType) =
      let expr' = applySubst' expr
      in  IR.TypeAppExpr srcSpan expr' typeExpr exprType
    applySubst' (IR.If srcSpan e1 e2 e3 exprType) =
      let e1' = applySubst' e1
          e2' = applySubst' e2
          e3' = applySubst' e3
      in  IR.If srcSpan e1' e2' e3' exprType
    applySubst' (IR.Case srcSpan expr alts exprType) =
      let expr' = applySubst' expr
          alts' = map (applySubst subst) alts
      in  IR.Case srcSpan expr' alts' exprType
    applySubst' (IR.Lambda srcSpan args expr exprType) =
      let (subst', args') = newRenameArgs subst args
          expr'           = applySubst subst' expr
      in  IR.Lambda srcSpan args' expr' exprType

    -- All other expressions remain unchanged.
    applySubst' expr@(IR.Con _ _ _       ) = expr
    applySubst' expr@(IR.Undefined _ _   ) = expr
    applySubst' expr@(IR.ErrorExpr  _ _ _) = expr
    applySubst' expr@(IR.IntLiteral _ _ _) = expr

-- | Applies the given expression substitution to the right-hand side of the
--   given @case@-expression alterntaive.
instance ApplySubst IR.Expr IR.Alt where
  applySubst subst (IR.Alt srcSpan conPat varPats expr) =
    let (subst', varPats') = newRenameArgs subst varPats
        expr'              = applySubst subst' expr
    in  IR.Alt srcSpan conPat varPats' expr'

-------------------------------------------------------------------------------
-- Application to types in expressions                                       --
-------------------------------------------------------------------------------

-- | Applies the given type substitution to an expression.
instance ApplySubst IR.Type IR.Expr where
  applySubst subst = applySubst'
   where
    applySubst' :: IR.Expr -> IR.Expr

    applySubst' (IR.Con srcSpan conName exprType) =
      let exprType' = applySubst subst exprType
      in  IR.Con srcSpan conName exprType'

    applySubst' (IR.Var srcSpan varName exprType) =
      let exprType' = applySubst subst exprType
      in  IR.Var srcSpan varName exprType'

    applySubst' (IR.App srcSpan e1 e2 exprType) =
      let e1'       = applySubst' e1
          e2'       = applySubst' e2
          exprType' = applySubst subst exprType
      in  IR.App srcSpan e1' e2' exprType'

    applySubst' (IR.TypeAppExpr srcSpan expr typeExpr exprType) =
      let expr'     = applySubst' expr
          typeExpr' = applySubst subst typeExpr
          exprType' = applySubst subst exprType
      in  IR.TypeAppExpr srcSpan expr' typeExpr' exprType'

    applySubst' (IR.If srcSpan e1 e2 e3 exprType) =
      let e1'       = applySubst' e1
          e2'       = applySubst' e2
          e3'       = applySubst' e3
          exprType' = applySubst subst exprType
      in  IR.If srcSpan e1' e2' e3' exprType'

    applySubst' (IR.Case srcSpan expr alts exprType) =
      let expr'     = applySubst' expr
          alts'     = applySubst subst alts
          exprType' = applySubst subst exprType
      in  IR.Case srcSpan expr' alts' exprType'

    applySubst' (IR.Undefined srcSpan exprType) =
      let exprType' = applySubst subst exprType
      in  IR.Undefined srcSpan exprType'

    applySubst' (IR.ErrorExpr srcSpan msg exprType) =
      let exprType' = applySubst subst exprType
      in  IR.ErrorExpr srcSpan msg exprType'

    applySubst' (IR.IntLiteral srcSpan value exprType) =
      let exprType' = applySubst subst exprType
      in  IR.IntLiteral srcSpan value exprType'

    applySubst' (IR.Lambda srcSpan args expr exprType) =
      let args'     = applySubst subst args
          expr'     = applySubst' expr
          exprType' = applySubst subst exprType
      in  IR.Lambda srcSpan args' expr' exprType'

-- | Applies the given type substitution to the right-hand side of the
--   given @case@-expression alterntaive.
instance ApplySubst IR.Type IR.Alt where
  applySubst subst (IR.Alt srcSpan conPat varPats expr) =
    let varPats' = applySubst subst varPats
        expr'    = applySubst subst expr
    in  IR.Alt srcSpan conPat varPats' expr'

-- | Applies the given type substitution to the type annotation of the given
--   variable pattern.
instance ApplySubst IR.Type IR.VarPat where
  applySubst subst (IR.VarPat srcSpan varIdent maybeVarType isStrict) =
    let maybeVarType' = applySubst subst maybeVarType
    in  IR.VarPat srcSpan varIdent maybeVarType' isStrict

-------------------------------------------------------------------------------
-- Application to function declarations.                                     --
-------------------------------------------------------------------------------

-- | Applies the given expression substitution to the right-hand side of a
--   function declaration.
instance ApplySubst IR.Expr IR.FuncDecl where
  applySubst subst (IR.FuncDecl srcSpan declIdent typeArgs args maybeRetType rhs)
    = let (subst', args') = newRenameArgs subst args
          rhs'            = applySubst subst' rhs
      in  IR.FuncDecl srcSpan declIdent typeArgs args' maybeRetType rhs'

-- | Applies the given type substitution to the right-hand side of a
--   function declaration.
instance ApplySubst IR.Type IR.FuncDecl where
  applySubst subst (IR.FuncDecl srcSpan declIdent typeArgs args maybeRetType rhs)
    = let args'         = applySubst subst args
          rhs'          = applySubst subst rhs
          maybeRetType' = applySubst subst maybeRetType
      in  IR.FuncDecl srcSpan declIdent typeArgs args' maybeRetType' rhs'

-------------------------------------------------------------------------------
-- Application to type expressions                                           --
-------------------------------------------------------------------------------

-- | Applies the given type substitution to a type expression.
instance ApplySubst IR.Type IR.Type where
  applySubst (Subst substMap) = applySubst'
   where
    applySubst' :: IR.Type -> IR.Type
    applySubst' typeCon@(IR.TypeCon _       _    ) = typeCon
    applySubst' typeVar@(IR.TypeVar srcSpan ident) = maybe
      typeVar
      ($ srcSpan)
      (Map.lookup (IR.UnQual (IR.Ident ident)) substMap)
    applySubst' (IR.TypeApp srcSpan t1 t2) =
      let t1' = applySubst' t1
          t2' = applySubst' t2
      in  IR.TypeApp srcSpan t1' t2'
    applySubst' (IR.FuncType srcSpan t1 t2) =
      let t1' = applySubst' t1
          t2' = applySubst' t2
      in  IR.FuncType srcSpan t1' t2'

-------------------------------------------------------------------------------
-- Application to type schemas                                           --
-------------------------------------------------------------------------------

-- | Applies the given type substitution to a type schema.
instance ApplySubst IR.Type IR.TypeSchema where
  applySubst subst (IR.TypeSchema srcSpan typeArgs typeExpr) =
    let (subst', typeArgs') = newRenameArgs subst typeArgs
        typeExpr'           = applySubst subst' typeExpr
    in  IR.TypeSchema srcSpan typeArgs' typeExpr'

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
  getScope :: arg -> IR.Scope

  -- | Converts the given argument to an expression that refers to
  --   the argument.
  toExpr :: arg -> SrcSpan -> expr

-- | Type variable declarations bind type variables in type expressions and
--   can be renamed.
instance Renamable IR.TypeVarDecl IR.Type where
  getIdent = IR.typeVarDeclIdent
  setIdent typeArg ident' = typeArg { IR.typeVarDeclIdent = ident' }
  getScope = const IR.TypeScope
  toExpr   = flip IR.TypeVar . getIdent

-- | Variable patterns bind variables in expressions and can be renamed.
instance Renamable IR.VarPat IR.Expr where
  getIdent = IR.varPatIdent
  setIdent varPat ident' = varPat { IR.varPatIdent = ident' }
  getScope = const IR.ValueScope
  toExpr   = flip IR.untypedVar . IR.UnQual . IR.Ident . getIdent

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
  let subst' = subst `substWithout` map (IR.UnQual . IR.Ident . getIdent) args
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
  argName :: IR.QName
  argName = IR.UnQual (IR.Ident argIdent)

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
freeSubstIdents :: HasRefs a => IR.Scope -> Subst a -> Set String
freeSubstIdents scope (Subst substMap) =
  Set.fromList
    $ mapMaybe (IR.identFromQName . refName)
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
  :: [IR.TypeVarDecl] -> Converter ([IR.TypeVarDecl], Subst IR.Type)
renameTypeArgsSubst typeArgDecls = do
  typeArgDecls' <- mapM freshTypeArgDecl typeArgDecls
  let typeArgNames = map IR.typeVarDeclQName typeArgDecls
      typeArgs'    = map (flip IR.TypeVar . IR.typeVarDeclIdent) typeArgDecls'
      subst        = composeSubsts (zipWith singleSubst' typeArgNames typeArgs')
  return (typeArgDecls', subst)
 where
  -- | Generates a fresh identifier for the given type argument and returns
  --   a type argument that preserves the source span of the original
  --   declaration.
  freshTypeArgDecl :: IR.TypeVarDecl -> Converter IR.TypeVarDecl
  freshTypeArgDecl (IR.TypeVarDecl srcSpan ident) = do
    ident' <- freshHaskellIdent ident
    return (IR.TypeVarDecl srcSpan ident')

-- | Renames the given type variables in the given expression or type
--   to fresh type variables.
renameTypeArgs
  :: ApplySubst IR.Type a
  => [IR.TypeVarDecl]
  -> a
  -> Converter ([IR.TypeVarDecl], a)
renameTypeArgs typeArgDecls x = do
  (typeArgDecls', subst) <- renameTypeArgsSubst typeArgDecls
  return (typeArgDecls', applySubst subst x)

-- | Creates a substitution that renames the arguments bound by the given
--   variable patterns to fresh variables.
--
--   Returns the new names for the variables and the substitution.
renameArgsSubst :: [IR.VarPat] -> Converter ([IR.VarPat], Subst IR.Expr)
renameArgsSubst args = do
  args' <- mapM freshVarPat args
  let argNames = map IR.varPatQName args
      argVars' = map (flip IR.untypedVar . IR.varPatQName) args'
      argSubst = composeSubsts (zipWith singleSubst' argNames argVars')
  return (args', argSubst)
 where
  -- | Generates a fresh identifier for the given variable pattern and returns
  --   a variable pattern that preserves the source span of the original
  --   pattern.
  freshVarPat :: IR.VarPat -> Converter IR.VarPat
  freshVarPat (IR.VarPat srcSpan varIdent maybeVarType isStrict) = do
    varIdent' <- freshHaskellIdent varIdent
    return (IR.VarPat srcSpan varIdent' maybeVarType isStrict)

-- | Renames the arguments bound by the given variable patterns in the given
--   expression to fresh variables.
--
--   Returns the new names for the variables and the resulting expression.
renameArgs
  :: ApplySubst IR.Expr a => [IR.VarPat] -> a -> Converter ([IR.VarPat], a)
renameArgs args x = do
  (args', subst) <- renameArgsSubst args
  return (args', applySubst subst x)
