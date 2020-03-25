-- | This module contains functions for importing module interfaces into
--   environments.

module Compiler.Environment.Importer
  ( importEntries
  , importInterface
  )
where

import qualified Data.Set                      as Set
import           Compiler.Environment
import           Compiler.Environment.Entry

-- | Inserts multiple entries into the given environment and associates them
--   with their original names.
importEntries :: [EnvEntry] -> Environment -> Environment
importEntries = flip (foldr addEntry)

-- | Imports all entries from the given module interface into the given
--   interface.
--
--   This function imports entries that are not exported by the given
--   interface as well.
importInterface :: ModuleInterface -> Environment -> Environment
importInterface = importEntries . Set.toList . interfaceEntries
