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

import           Data.Composition               ( (.:) )
import           Control.Monad.Identity

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

-- | Resolves all type names referenced by the given type expression
--   to their original name.
resolveTypes :: HS.Type -> Converter HS.Type
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

-- | Replaces all constructor names in the given type expression
--   by the name returned by the given function.
resolveTypesWithM
  :: Monad m => (SrcSpan -> HS.QName -> m HS.QName) -> HS.Type -> m HS.Type
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
