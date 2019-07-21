module Compiler.Converter.Fresh where

import           Compiler.Converter.Renamer
import           Compiler.Converter.State

-- | Gets the next fresh Haskell identifier from the current environment.
--
--   Fresh identifiers are identifiers that have been introduced aritifically
--   into the Haskell or Coq AST. All fresh identifiers start with an at-sign
--   by convention in Haskell. This ensures that they cannot be confused with
--   actual Haskell identifiers. They are translated to Coq identifiers that
--   start with an underscore by the renamer.
--
--   The freshly generated identifier is not inserted into the environment,
--   i.e. it can still be used to create a declaration.
freshHaskellIdent :: Converter String
freshHaskellIdent = do
  env <- getEnv
  let count = freshIdentCount env
  putEnv (env { freshIdentCount = count + 1 })
  return ("@" ++ show count)

-- | Gets the next fresh Haskell identifier from the current environment
--   and renames it such that it can be used in Coq.
freshCoqIdent :: Converter String
freshCoqIdent = do
  ident  <- freshHaskellIdent
  ident' <- inEnv $ renameIdent ident
  return ident'
