module Compiler.Environment.ModuleInterface where

import           Data.Set                       ( Set )

import qualified Compiler.Backend.Coq.Syntax   as G
import           Compiler.Environment.Entry
import           Compiler.Environment.Scope
import qualified Compiler.IR.Syntax            as HS

-- | Data type that contains the information of a module environment that
--   is exported and imported.
data ModuleInterface = ModuleInterface
  { interfaceModName :: HS.ModName
    -- ^ The name of the module.
  , interfaceLibName :: G.ModuleIdent
    -- ^ The name of the Coq library that contains this module (e.g. @"Base"@
    --   for the @Prelude@ module).
  , interfaceExports :: Set ScopedName
    -- ^ The names (qualified with their original module name) that are
    --   exported by the module.
  , interfaceEntries :: Set EnvEntry
    -- ^ The entries (including hidden entries) defined in or imported
    --   by the module.
  }
 deriving Show
