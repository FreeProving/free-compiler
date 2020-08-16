-- | This module contains the data type that is used to represent module
--   interfaces.
--
--   A module interface contains all environment entries that are defined in
--   the module and all entries of the interfaces of imported modules.
--   The entries which are actually exported by the module (and thus visible
--   to modules that import it) are also recorded in the module interface.
--   Entries which are part of the module interface but not actually exported
--   by the module are called hidden entries.
--
--   The module interface must contain hidden entries such that type synonyms
--   can be expanded properly. The entry of a type synonym can contain type
--   constructors which were in scope when the type synonym was declared but
--   don't have to be in scope when the imported type synonym is used.
module FreeC.Environment.ModuleInterface where

import           Data.Set ( Set )

import qualified FreeC.Backend.Agda.Syntax as Agda
import qualified FreeC.Backend.Coq.Syntax as Coq
import           FreeC.Environment.Entry
import qualified FreeC.IR.Syntax as IR

-- | Data type that contains the information of a module environment that
--   is exported and imported.
data ModuleInterface = ModuleInterface
  { interfaceModName     :: IR.ModName
    -- ^ The name of the module.
  , interfaceLibName     :: Coq.ModuleIdent
    -- ^ The name of the Coq library that contains this module (e.g. @"Base"@
    --   for the @Prelude@ module).
  , interfaceAgdaLibName :: Agda.Name
    -- ^ The name of the Agda library that contains this module (e.g. @"Base"@
    --   for the @Prelude@ module).
  , interfaceExports     :: Set IR.ScopedName
    -- ^ The names (qualified with their original module name) that are
    --   exported by the module.
  , interfaceEntries     :: Set EnvEntry
    -- ^ The entries (including hidden entries) defined in or imported
    --   by the module.
  }
 deriving Show
