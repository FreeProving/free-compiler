-- | This module contains functions for importing module interfaces into
--   environments.

module FreeC.Environment.Importer
  ( importEntries
  , importInterface
  )
where

import qualified Data.Set                      as Set
import           FreeC.Environment
import           FreeC.Environment.ModuleInterface
import           FreeC.Environment.Entry
