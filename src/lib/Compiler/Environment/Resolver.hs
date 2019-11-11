-- | This module contains functions for converting unqualified identifiers to
--   qualified identifiers.

module Compiler.Environment.Resolver where

import           Compiler.Environment.Entry
import           Compiler.Environment.LookupOrFail
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

-- | Resolves all type names referenced by the given entry of the environment.
resolveReferences :: EnvEntry -> Converter EnvEntry
resolveReferences entry
  | isTypeSynEntry entry = do
    typeSyn <- resolveTypes (entryTypeSyn entry)
    return entry { entryTypeSyn = typeSyn }
  | isConEntry entry || isFuncEntry entry = do
    argTypes   <- mapM (mapM resolveTypes) (entryArgTypes entry)
    returnType <- mapM resolveTypes (entryReturnType entry)
    return entry { entryArgTypes = argTypes, entryReturnType = returnType }
  | otherwise = return entry

-- | Replaces all constructor names in the given type expression by the
--   original name of the corresponding entry of the current environment.
--
--   All referenced entries must be in the environment and unambigious.
resolveTypes :: HS.Type -> Converter HS.Type
resolveTypes var@(HS.TypeVar _       _   ) = return var
resolveTypes (    HS.TypeCon srcSpan name) = do
  entry <- lookupEntryOrFail srcSpan TypeScope name
  return (HS.TypeCon srcSpan (entryName entry))
resolveTypes (HS.TypeApp srcSpan t1 t2) = do
  t1' <- resolveTypes t1
  t2' <- resolveTypes t2
  return (HS.TypeApp srcSpan t1' t2')
resolveTypes (HS.TypeFunc srcSpan t1 t2) = do
  t1' <- resolveTypes t1
  t2' <- resolveTypes t2
  return (HS.TypeFunc srcSpan t1' t2')
