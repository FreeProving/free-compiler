-- | This module contains functions for importing module interfaces into
--   environments.

module Compiler.Environment.Importer
  ( importEntry
  , importEntries
  , importInterface
  , importInterfaceAs
  )
where

import qualified Data.Set                      as Set
import           Data.Tuple.Extra               ( (&&&) )

import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.Resolver
import qualified Compiler.Haskell.AST          as HS

-------------------------------------------------------------------------------
-- Importing entries                                                         --
-------------------------------------------------------------------------------

-- | Inserts an entry into the given environment and associates it with the
--   given name.
--
--   In contrast to 'addEntry' the entry is not added at the current 'envDepth'
--   but at depth @-1@ which indicates that it is not a top level entry but
--   an external entry and should not be exported.
importEntry :: HS.QName -> EnvEntry -> Environment -> Environment
importEntry name entry env = addEntry' name entry (-1) env

-- | Inserts multiple entries into the given environment and associates them
--   with the corresponding name.
importEntries :: [(HS.QName, EnvEntry)] -> Environment -> Environment
importEntries = flip (foldr (uncurry importEntry))

-------------------------------------------------------------------------------
-- Importing modules                                                         --
-------------------------------------------------------------------------------

-- | Imports all entries from the given module interface into the given
--   interface.
--
--   This function imports only entries that are exported by the given
--   interface.
importInterface :: ModuleInterface -> Environment -> Environment
importInterface iface =
  importEntries
    $ map (unqualify . entryName &&& id)
    $ filter (isExportedBy iface)
    $ interfaceEntries' iface

-- | Like 'importInterface' but all exported entries are qualifed with the
--   given module name.
importInterfaceAs :: HS.ModName -> ModuleInterface -> Environment -> Environment
importInterfaceAs alias iface = importEntries
  (hiddenEntries ++ exportedEntries)
 where
  -- | Tests wheter the given entry is exported by the imported interface.
  isExported :: EnvEntry -> Bool
  isExported = flip Set.member (interfaceExports iface) . entryScopedName

  -- | All entries (including hidden entries) of the given interface.
  --
  --   References in the entries (i.e., used type constructors) are
  --   converted to hidden names (see 'hide').
  entries :: [EnvEntry]
  entries = interfaceEntries' iface

  -- | Entries of the interface that have been exported explicitly
  --   (i.e., no hidden entries).
  --
  --   All exported entries are brought into scope qualified with the 'alias'.
  exportedEntries :: [(HS.QName, EnvEntry)]
  exportedEntries =
    map (qualifyWith alias . entryName &&& id) (filter isExported entries)

  -- | Entries (including hidden entries) of the interface.
  hiddenEntries :: [(HS.QName, EnvEntry)]
  hiddenEntries = map (hide . entryName &&& id) entries

-------------------------------------------------------------------------------
-- Auxilary functions                                                        --
-------------------------------------------------------------------------------

-- | Tests wheter the given entry is exported by the given interface.
isExportedBy :: ModuleInterface -> EnvEntry -> Bool
isExportedBy iface = flip Set.member (interfaceExports iface) . entryScopedName

-- | All entries (including hidden entries) of the given interface.
--
--   References in the entries (i.e., used type constructors) are
--   converted to hidden names (see 'hide').
interfaceEntries' :: ModuleInterface -> [EnvEntry]
interfaceEntries' =
  map (resolveReferencesWith (const hide)) . Set.toList . interfaceEntries

-- | Removes the module name from a qualified name.
unqualify :: HS.QName -> HS.QName
unqualify (HS.UnQual name) = HS.UnQual name
unqualify (HS.Qual _ name) = HS.UnQual name

-- | Qualifies the name of an imported entry with given module name.
qualifyWith :: HS.ModName -> HS.QName -> HS.QName
qualifyWith modName (HS.Qual _ name) = HS.Qual modName name
qualifyWith modName (HS.UnQual name) = HS.Qual modName name

-- | Changes the name of a hidden entry such that it cannot be accessed
--   directly by the user.
hide :: HS.QName -> HS.QName
hide (HS.Qual modName name) = HS.Qual (HS.internalIdentChar : modName) name
hide (HS.UnQual name      ) = HS.UnQual name
