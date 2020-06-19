-- | This module contains functions for generating fresh identifiers.
--
--   Fresh identifiers are identifiers that have been introduced artificially
--   into the Haskell or Coq AST. They are guaranteed not to conflict with any
--   other valid identifier.

module FreeC.Environment.Fresh
  ( -- * Prefixes
    freshArgPrefix
  , freshFuncPrefix
  , freshBoolPrefix
  , freshTypeVarPrefix
  , freshTypeArgPrefix
    -- * Generating fresh Haskell identifiers
  , freshHaskellIdent
  , freshHaskellName
  , freshHaskellQName
  , freshTypeVar
    -- * Generating fresh Coq identifiers
  , freshCoqIdent
  , freshCoqQualid
  )
where

import           Data.List                      ( elemIndex )
import           Data.Maybe                     ( fromJust )
import qualified Data.Map.Strict               as Map

import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.Renamer
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter

-------------------------------------------------------------------------------
-- Prefixes                                                                  --
-------------------------------------------------------------------------------

-- | The prefix to use for artificially introduced variables of type @a@.
freshArgPrefix :: String
freshArgPrefix = "x"

-- | The prefix to use for artificially introduced variables of type @a -> b@.
freshFuncPrefix :: String
freshFuncPrefix = "f"

-- | The prefix to use for artificially introduced variables of type @Bool@.
freshBoolPrefix :: String
freshBoolPrefix = "cond"

-- | The prefix to use for artificially introduced type variables of kind @*@.
freshTypeVarPrefix :: String
freshTypeVarPrefix = "a"

-- | The prefix to use for artificially introduced type variables of kind @*@
--   that are passed as a type argument to a function.
freshTypeArgPrefix :: String
freshTypeArgPrefix = "t"

-------------------------------------------------------------------------------
-- Generating fresh Haskell identifiers                                      --
-------------------------------------------------------------------------------

-- | Gets the next fresh Haskell identifier from the current environment.
--
--   All fresh identifiers contain an at-sign (See 'IR.internalIdentChar').
--   This ensures that they cannot be confused with actual Haskell identifiers.
--   The corresponding Coq identifier contains an underscore instead (see
--   "FreeC.Environment.Renamer"). The at-sign (or underscore) is preceded
--   by the given prefix and followed by an incrementing number (staring at
--   @0@).
--
--   If the given prefix is a fresh identifier itself (i.e. contains an
--   at-sign), the prefix of that identifier is used instead.
--
--   The freshly generated identifier is not inserted into the environment,
--   i.e. it can still be used to create a declaration.
freshHaskellIdent :: String -> Converter String
freshHaskellIdent prefix = case elemIndex IR.internalIdentChar prefix of
  Just atIndex -> freshHaskellIdent (take atIndex prefix)
  Nothing      -> do
    env <- getEnv
    let count = Map.findWithDefault 0 prefix (envFreshIdentCount env)
    putEnv
      (env
        { envFreshIdentCount = Map.insert prefix
                                          (count + 1)
                                          (envFreshIdentCount env)
        }
      )
    return (prefix ++ IR.internalIdentChar : show count)

-- | Applies 'freshHaskellIdent' to the given name.
--
--   Fails if the given name is a symbol.
freshHaskellName :: IR.Name -> Converter IR.Name
freshHaskellName (IR.Ident ident) = IR.Ident <$> freshHaskellIdent ident
freshHaskellName (IR.Symbol _) =
  fail "freshHaskellName: expected identifier, got symbol"

-- | Like 'freshHaskellName' but preserves the module name of qualified names.
freshHaskellQName :: IR.QName -> Converter IR.QName
freshHaskellQName (IR.UnQual name) = IR.UnQual <$> freshHaskellName name
freshHaskellQName (IR.Qual modName name) =
  IR.Qual modName <$> freshHaskellName name

-- | Generates a fresh Haskell type variable.
freshTypeVar :: Converter IR.Type
freshTypeVar = do
  ident <- freshHaskellIdent freshTypeVarPrefix
  return (IR.TypeVar NoSrcSpan ident)

-------------------------------------------------------------------------------
-- Generating fresh Coq identifiers                                          --
-------------------------------------------------------------------------------

-- | Gets the next fresh Haskell identifier from the current environment
--   and renames it such that it can be used in Coq.
--
--   A 'VarEntry' is added to the environment for the Haskell identifier in the
--   'IR.FreshScope' name space. Since the fresh Haskell identifier is not
--   visible from the outside, the environment entry cannot be accessed
--   directly. Its main purpose is to prevent the the same fresh Coq identifier
--   to be issued twice.
freshCoqIdent :: String -> Converter String
freshCoqIdent = fmap (fromJust . Coq.unpackQualid) . freshCoqQualid

-- | Like 'freshCoqIdent' but the resulting Coq identifier is wrapped in a
--   'Coq.Qualid'.
freshCoqQualid :: String -> Converter Coq.Qualid
freshCoqQualid = fmap entryIdent . freshEntry

-------------------------------------------------------------------------------
-- Generating entries for fresh identifiers                                  --
-------------------------------------------------------------------------------

-- | Creates a new 'FreshEntry' from a fresh Haskell identifier with the
--   given prefix.
freshEntry :: String -> Converter EnvEntry
freshEntry prefix = do
  ident <- freshHaskellIdent prefix
  renameAndAddEntry FreshEntry { entryName  = IR.UnQual (IR.Ident ident)
                               , entryIdent = undefined -- filled by renamer
                               }
