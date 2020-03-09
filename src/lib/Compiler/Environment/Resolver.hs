-- | This module contains functions for converting unqualified identifiers to
--   qualified identifiers.

module Compiler.Environment.Resolver
  ( -- * Resolving to original name
    resolveReferences
  , resolveTypes
    -- * Resolving by custom function
  , resolveReferencesWith
  , resolveReferencesWithM
  )
where

import           Control.Monad.Identity
import           Data.Composition               ( (.:) )

import           Compiler.Environment.Entry
import           Compiler.Environment.LookupOrFail
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter

-------------------------------------------------------------------------------
-- Resolving to original name                                                --
-------------------------------------------------------------------------------

-- | Resolves all type names referenced by the given entry of the environment
--   to their original name.
resolveReferences :: EnvEntry -> Converter EnvEntry
resolveReferences = resolveReferencesWithM lookupOriginalName

-- | Resolves all type constructor names referenced by the given expression,
--   type expression or type schema to their original name.
resolveTypes :: ResolveTypes a => a -> Converter a
resolveTypes = resolveTypesWithM lookupOriginalName

-- | Looks up the original name of the entry with the given name.
lookupOriginalName :: SrcSpan -> HS.QName -> Converter HS.QName
lookupOriginalName srcSpan name = do
  entry <- lookupEntryOrFail srcSpan TypeScope name
  return (entryName entry)

-------------------------------------------------------------------------------
-- Resolving by custom function                                              --
-------------------------------------------------------------------------------

-- | Resolves all type names referenced by the given entry of the environment
--   by applying the given function.
--
--   All referenced entries must be in the environment and unambigious.
resolveReferencesWith
  :: (SrcSpan -> HS.QName -> HS.QName) -> EnvEntry -> EnvEntry
resolveReferencesWith =
  runIdentity .: applyToTypes . resolveTypesWithM . (return .:)

-- | Resolves all type names referenced by the given entry of the environment
--   by applying the given function monadically.
--
--   All referenced entries must be in the environment and unambigious.
resolveReferencesWithM
  :: Monad m => (SrcSpan -> HS.QName -> m HS.QName) -> EnvEntry -> m EnvEntry
resolveReferencesWithM = applyToTypes . resolveTypesWithM

-------------------------------------------------------------------------------
-- Resolving by custom function                                              --
-------------------------------------------------------------------------------

-- | Applies the given function to all types in the given entry monadically.
applyToTypes :: Monad m => (HS.Type -> m HS.Type) -> EnvEntry -> m EnvEntry
applyToTypes f entry
  | isTypeSynEntry entry = do
    typeSyn <- f (entryTypeSyn entry)
    return entry { entryTypeSyn = typeSyn }
  | isConEntry entry || isFuncEntry entry = do
    argTypes   <- mapM (mapM f) (entryArgTypes entry)
    returnType <- mapM f (entryReturnType entry)
    return entry { entryArgTypes = argTypes, entryReturnType = returnType }
  | otherwise = return entry

-- | Type class for AST nodes which contain type constructor references that
--   can be resolved to their original name.
class ResolveTypes a where
  resolveTypesWithM
    :: Monad m => (SrcSpan -> HS.QName -> m HS.QName) -> a -> m a

-- | Type constructors in type expressions can be resolved.
instance ResolveTypes HS.Type where
  -- | Replaces all constructor names in the given type expression
  --   by the name returned by the given function.
  resolveTypesWithM _ var@(HS.TypeVar _       _   ) = return var
  resolveTypesWithM f (    HS.TypeCon srcSpan name) = do
    name' <- f srcSpan name
    return (HS.TypeCon srcSpan name')
  resolveTypesWithM f (HS.TypeApp srcSpan t1 t2) = do
    t1' <- resolveTypesWithM f t1
    t2' <- resolveTypesWithM f t2
    return (HS.TypeApp srcSpan t1' t2')
  resolveTypesWithM f (HS.TypeFunc srcSpan t1 t2) = do
    t1' <- resolveTypesWithM f t1
    t2' <- resolveTypesWithM f t2
    return (HS.TypeFunc srcSpan t1' t2')

-- | Type constructors in type schemas can be resolved.
instance ResolveTypes HS.TypeSchema where
  resolveTypesWithM f (HS.TypeSchema srcSpan typeArgs typeExpr) = do
    typeExpr' <- resolveTypesWithM f typeExpr
    return (HS.TypeSchema srcSpan typeArgs typeExpr')

-- | Type constructors in type signatures and visible type applications
--   can be resolved.
instance ResolveTypes HS.Expr where
  -- Resolve types in type or type schema.
  resolveTypesWithM f (HS.TypeAppExpr srcSpan expr typeExpr) = do
    expr'     <- resolveTypesWithM f expr
    typeExpr' <- resolveTypesWithM f typeExpr
    return (HS.TypeAppExpr srcSpan expr' typeExpr')
  resolveTypesWithM f (HS.ExprTypeSig srcSpan expr typeSchema) = do
    expr'       <- resolveTypesWithM f expr
    typeSchema' <- resolveTypesWithM f typeSchema
    return (HS.ExprTypeSig srcSpan expr' typeSchema')

  -- Resolve types recursively.
  resolveTypesWithM f (HS.App srcSpan e1 e2) = do
    e1' <- resolveTypesWithM f e1
    e2' <- resolveTypesWithM f e2
    return (HS.App srcSpan e1' e2')
  resolveTypesWithM f (HS.If srcSpan e1 e2 e3) = do
    e1' <- resolveTypesWithM f e1
    e2' <- resolveTypesWithM f e2
    e3' <- resolveTypesWithM f e3
    return (HS.If srcSpan e1' e2' e3')
  resolveTypesWithM f (HS.Case srcSpan expr alts) = do
    expr' <- resolveTypesWithM f expr
    alts' <- mapM (resolveTypesWithM f) alts
    return (HS.Case srcSpan expr' alts')
  resolveTypesWithM f (HS.Lambda srcSpan args expr) = do
    args' <- mapM (resolveTypesWithM f) args
    expr' <- resolveTypesWithM f expr
    return (HS.Lambda srcSpan args' expr')

  -- All other expressions remain unchanged.
  resolveTypesWithM _ expr@(HS.Con        _ _) = return expr
  resolveTypesWithM _ expr@(HS.Var        _ _) = return expr
  resolveTypesWithM _ expr@(HS.IntLiteral _ _) = return expr
  resolveTypesWithM _ expr@(HS.Undefined _   ) = return expr
  resolveTypesWithM _ expr@(HS.ErrorExpr _ _ ) = return expr

-- | Type constructors in type signatures and visible type applications on
--   the right-hand side of a @case@ expression alternative can be resolved.
instance ResolveTypes HS.Alt where
  resolveTypesWithM f (HS.Alt srcSpan conPat varPats expr) = do
    varPats' <- mapM (resolveTypesWithM f) varPats
    expr'    <- resolveTypesWithM f expr
    return (HS.Alt srcSpan conPat varPats' expr')

-- | Type constructors in the type signatures of variable patterns in function
--   declarations and on the right-hand side can be resolved.
instance ResolveTypes HS.FuncDecl where
  resolveTypesWithM f (HS.FuncDecl srcSpan declIdent typeArgs args rhs maybeRetType) = do
    args' <- mapM (resolveTypesWithM f) args
    rhs'  <- resolveTypesWithM f rhs
    maybeRetType' <- mapM (resolveTypesWithM f) maybeRetType
    return (HS.FuncDecl srcSpan declIdent typeArgs args' rhs' maybeRetType')

-- | If a variable pattern has a type signature, type constructors in the
--   annotated type can be resolved.
instance ResolveTypes HS.VarPat where
  resolveTypesWithM f (HS.VarPat srcSpan ident maybeVarType) = do
    maybeVarType' <- mapM (resolveTypesWithM f) maybeVarType
    return (HS.VarPat srcSpan ident maybeVarType')
