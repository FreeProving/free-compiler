-- | This module contains functions for generating frsh identifiers.
--
--   Fresh identifiers are identifiers that have been introduced aritifically
--   into the Haskell or Coq AST. They are guranteed not to conflict with any
--   other valid identifier.

module Compiler.Converter.Fresh where

import qualified Data.Map.Strict               as Map

import           Compiler.Converter.Renamer
import           Compiler.Converter.State

-- | The prefix to use for artificially introduced function arguments.
freshArgPrefix :: String
freshArgPrefix = "x"

-- | Gets the next fresh Haskell identifier from the current environment.
--
--   All fresh identifiers start with an at-sign by convention. This ensures
--   that they cannot be confused with actual Haskell identifiers. They are
--   translated to Coq identifiers that start with an underscore by the
--   renamer. The at-sgn (or underscore) is followed by the given prefix and an
--   incrementing number (staring at @0@).
--
--   The freshly generated identifier is not inserted into the environment,
--   i.e. it can still be used to create a declaration.
freshHaskellIdent :: String -> Converter String
freshHaskellIdent prefix = do
  env <- getEnv
  let count = Map.findWithDefault 0 prefix (freshIdentCount env)
  putEnv
    (env { freshIdentCount = Map.insert prefix (count + 1) (freshIdentCount env)
         }
    )
  return ("@" ++ prefix ++ show count)

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
