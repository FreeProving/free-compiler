-- | This module contains functions for generating frsh identifiers.
--
--   Fresh identifiers are identifiers that have been introduced aritifically
--   into the Haskell or Coq AST. They are guranteed not to conflict with any
--   other valid identifier.

module Compiler.Environment.Fresh where

import qualified Data.Map.Strict               as Map
import           Data.List                      ( elemIndex )

import           Compiler.Environment
import           Compiler.Environment.Renamer
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

-- | The prefix to use for artificially introduced function arguments.
freshArgPrefix :: String
freshArgPrefix = "x"


-- | Gets the next fresh Haskell identifier from the current environment.
--
--   All fresh identifiers contain an at-sign (See 'HS.internalIdentChar').
--   This ensures that they cannot be confused with actual Haskell identifiers.
--   The corresponding Coq identifier contains an underscore instead (see
--   "Compiler.Environment.Renamer"). The at-sign (or underscore) is preceded
--   by the given prefix and followed by an incrementing number (staring at
--   @0@).
--
--   If the given prefix is a fresh identifier itself (i.e. contains an
--   at-sign), the prefix of that identifier is used instead.
--
--   The freshly generated identifier is not inserted into the environment,
--   i.e. it can still be used to create a declaration.
freshHaskellIdent :: String -> Converter String
freshHaskellIdent prefix = case elemIndex HS.internalIdentChar prefix of
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
    return (prefix ++ HS.internalIdentChar : show count)

-- | Gets the next fresh Haskell identifier from the current environment
--   and renames it such that it can be used in Coq.
--
--   The freshly generated identifier is not inserted into the environment,
--   i.e. it can still be used to create a declaration.
freshCoqIdent :: String -> Converter String
freshCoqIdent prefix = do
  ident  <- freshHaskellIdent prefix
  ident' <- inEnv $ renameIdent ident
  return ident'
