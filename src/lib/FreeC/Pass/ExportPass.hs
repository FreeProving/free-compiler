-- | This module contains a compiler pass that adds a module interface for the
--   translated module to the environment.
--
--   The interface contains all top-level entries that are currently in the
--   environment. Only entries that are defined in the translated module
--   are listed as exported. All other entries are "hidden". Hidden entries are
--   included such that module interfaces are self contained and type synonyms
--   can be expanded properly.
--   Additionally, all Coq identifiers of exported entries are qualified with
--   their original module name in the module interface.
--   This prevents name conflicts when several modules that use the same identifier
--   are imported.
--
--   = Examples
--
--   == Example 1
--
--   The module interface for the following module
--
--   > module A where
--   >
--   > data Foo = Bar
--
--   contains 'interfaceEntries' for all entries from the implicitly imported
--   @Prelude@ module and an entry for the type @A.Foo@ and constructor @A.Bar@.
--   However, only @A.Foo@ and @A.Bar@ are exported by the module and
--   therefore listed in 'interfaceExports'.
--
--   == Example 2
--
--   When a module imports the module @A@ from the example above,
--
--   > module B where
--   >
--   > import A
--   >
--   > foo :: a -> Foo
--   > foo x = Bar
--
--   its interface contains again all entries from the implicitly imported
--   @Prelude@ module, the entries from @A@'s module interface and the entry
--   for the top-level function @B.foo@. Entries for local variables such as
--   @x@ are not part of @B@'s interface. Since 'interfaceEntries' is a set,
--   the @Prelude@ entries which are both implicitly imported by @B@ and part
--   of the imported interface from @A@ are not listed twice in @B@'s interface.
--
--   = Specification
--
--   == Preconditions
--
--   The environment must contain all entries for declarations that should
--   be exported.
--
--   ==  Translation
--
--   No modifications are made to the AST. A module interface is added to
--   the environment.
--
--   == Postcondition
--
--   The environment contains a module interface for the translated module.
module FreeC.Pass.ExportPass
  ( exportPass
  )
where

import qualified Data.Map.Strict               as Map
import qualified Data.Set                      as Set
import qualified Data.Text                     as Text

import           Language.Coq.Gallina

import qualified FreeC.Backend.Coq.Base        as Coq.Base
import           FreeC.Environment
import           FreeC.Environment.ModuleInterface
import           FreeC.Environment.Entry
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Pass

-- | A compiler pass that constructs a module interface from the current
--   environment for the given module and inserts it into the environment.
exportPass :: Pass IR.Module
exportPass ast = do
  iface <- exportInterface (IR.modName ast)
  modifyEnv $ makeModuleAvailable iface
  return ast

-- | Generates a module interface that contains all entries from the
--   environment and exports all top-level declarations that are declared in
--   the module with the given name.
exportInterface :: IR.ModName -> Converter ModuleInterface
exportInterface modName = do
  entries <- inEnv $ Map.elems . envEntries
  let exports     = map entryScopedName $ filter isExported entries
  let qualEntries = map qualifyExportedIdent entries
  return
    (ModuleInterface { interfaceModName = modName
                     , interfaceLibName = Coq.Base.generatedLibName
                     , interfaceExports = Set.fromList exports
                     , interfaceEntries = Set.fromList qualEntries
                     }
    )
 where
   -- Tests whether to export the given entry.
   --
   -- Only top-level entries that are declared in the module are exported.
   -- Since the original names of entries are qualified with the name of the
   -- module they are declared in, we can tell whether an entry is declared
   -- in the exported module by comparing the prefix of its original name
   -- with the module name.
  isExported :: EnvEntry -> Bool
  isExported entry = case entryName entry of
    IR.Qual modName' _ -> modName' == modName
    IR.UnQual _        -> False

  -- Qualifies the Coq identifier in the module interface with the module name
  -- when an entry of the module is exported.
  -- This ensures that any module that imports the entry uses its qualified
  -- name, which prevents name conflicts between imported modules.
  qualifyExportedIdent :: EnvEntry -> EnvEntry
  qualifyExportedIdent entry
    | isExported entry = if isConEntry entry
      then entry { entryIdent      = qualifyIdent (entryIdent entry)
                 , entrySmartIdent = qualifyIdent (entrySmartIdent entry)
                 }
      else entry { entryIdent = qualifyIdent (entryIdent entry) }
    | otherwise = entry


  -- Qualifies an unqualified Coq identifier with the module name.
  -- A qualified Coq identifer is not modified.
  qualifyIdent :: Qualid -> Qualid
  qualifyIdent (         Bare coqName ) = Qualified (Text.pack modName) coqName
  qualifyIdent qualName@(Qualified _ _) = qualName
