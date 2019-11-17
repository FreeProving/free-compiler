-- | This module contains a data type that encapsulates the state of
--   the compiler. There are also utility functions to modify the state and
--   retreive information stored in the state.

module Compiler.Environment
  ( -- * Module interface
    ModuleInterface(..)
    -- * Environment
  , Environment(..)
  , emptyEnv
  , childEnv
  -- * Module information
  , makeModuleAvailable
  , isModuleAvailable
  , lookupAvailableModule
  -- * Import and export entries
  , importEntry
  , importInterface
  , importInterfaceAs
  -- * Inserting entries into the environment
  , addEntry
  , defineDecArg
  , defineTypeSig
  -- * Looking up entries from the environment
  , lookupEntries
  , lookupEntry
  , existsLocalEntry
  , isFunction
  , isPureVar
  , lookupIdent
  , lookupSmartIdent
  , usedIdents
  , lookupSrcSpan
  , lookupTypeArgs
  , lookupArgTypes
  , lookupReturnType
  , lookupArity
  , lookupTypeSynonym
  , lookupTypeSig
  , isPartial
  , lookupDecArg
  -- * QuickCheck support
  , enableQuickCheck
  , isQuickCheckEnabled
  )
where

import           Data.Composition               ( (.:)
                                                , (.:.)
                                                )
import           Data.List                      ( find
                                                , partition
                                                )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( isJust )
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
import           Data.Tuple.Extra               ( (&&&) )
import           Control.Monad                  ( join )

import qualified Compiler.Coq.AST              as G
import           Compiler.Environment.Entry
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Util.Predicate

-------------------------------------------------------------------------------
-- Module interface                                                          --
-------------------------------------------------------------------------------

-- | Data type that contains the information of a module environment that
--   is exported and imported.
data ModuleInterface = ModuleInterface
  { interfaceModName :: HS.ModName
    -- ^ The name of the module.
  , interfaceExports :: Set ScopedName
    -- ^ The names (qualified with their original module name) that are
    --   exported by the module.
  , interfaceEntries :: Set EnvEntry
    -- ^ The entries (including hidden entries) defined in or imported
    --   by the module.
  }
 deriving Show

-------------------------------------------------------------------------------
-- Environment                                                               --
-------------------------------------------------------------------------------

-- | Data type that encapsulates the state of the converter.
data Environment = Environment
  { envDepth :: Int
    -- ^ The number of parent environments.

  , envModName :: HS.ModName
    -- ^ The name of the currently translated module.
    --   Defaults to the empty string.
  , envAvailableModules :: Map HS.ModName ModuleInterface
    -- ^ Maps names of modules that can be imported to their interface.

  , envEntries :: Map ScopedName (Set EnvEntry, Int)
    -- ^ Maps Haskell names to entries for declarations.
    --   In addition to the entry, the 'envDepth' of the environment is
    --   recorded.
    --   There can be multiple entries with the same name as long as they are
    --   not referenced. Entries are identified by their original name.
  , envTypeSigs :: Map HS.QName HS.Type
    -- ^ Maps names of Haskell functions to their annotated types.
  , envDecArgs :: Map HS.QName Int
    -- ^ Maps Haskell function names to the index of their decreasing argument.
    --   Contains no entry for non-recursive functions, but there are also
    --   entries for functions that are shadowed by local variables.
  , envFreshIdentCount :: Map String Int
    -- ^ The number of fresh identifiers that were used in the environment
    --   with a certain prefix.

  , envQuickCheckEnabled :: Bool
    -- ^ Whether the translation of QuickCheck properties is enabled in the
    --   current environment (i.e. the module imports @Test.QuickCheck@).
  }
 deriving Show

-- | An environment that does not even contain any predefined types and
--   functions.
emptyEnv :: Environment
emptyEnv = Environment
  { envDepth             = 0
    -- Modules
  , envModName           = ""
  , envAvailableModules  = Map.empty
    -- Entries
  , envEntries           = Map.empty
  , envTypeSigs          = Map.empty
  , envDecArgs           = Map.empty
  , envFreshIdentCount   = Map.empty
    -- QuickCheck
  , envQuickCheckEnabled = False
  }

-- | Creates a child environment of the given environment.
childEnv :: Environment -> Environment
childEnv env = env { envDepth = envDepth env + 1 }

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Inserts the interface of a module name into the environment such that it
--   can be imported.
makeModuleAvailable :: ModuleInterface -> Environment -> Environment
makeModuleAvailable iface env = env
  { envAvailableModules = Map.insert (interfaceModName iface)
                                     iface
                                     (envAvailableModules env)
  }

-- | Tests whether the module with the given name can be imported.
isModuleAvailable :: HS.ModName -> Environment -> Bool
isModuleAvailable = isJust .: lookupAvailableModule

-- | Looks up the environment of another module that can be imported.
lookupAvailableModule :: HS.ModName -> Environment -> Maybe ModuleInterface
lookupAvailableModule modName = Map.lookup modName . envAvailableModules

-------------------------------------------------------------------------------
-- Import and export entries                                                 --
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

-- | Imports all entries from the given module interface into the given
--   interface.
--
--   This function imports only entries that are exported by the given
--   interface.
importInterface :: ModuleInterface -> Environment -> Environment
importInterface iface =
  importEntries
    $ map (unqualify . entryName &&& id)
    $ filter isExported
    $ Set.toList
    $ interfaceEntries iface
 where
  -- | Tests wheter the given entry is exported by the imported interface.
  isExported :: EnvEntry -> Bool
  isExported = flip Set.member (interfaceExports iface) . entryScopedName

  -- | Removes the module name from a qualified name.
  unqualify :: HS.QName -> HS.QName
  unqualify (HS.UnQual name) = HS.UnQual name
  unqualify (HS.Qual _ name) = HS.UnQual name

-- | Like 'importInterface' but all exported entries are qualifed with the
--   given module name.
importInterfaceAs :: HS.ModName -> ModuleInterface -> Environment -> Environment
importInterfaceAs modName iface = importHiddenEntries . importExportedEntries
 where
  -- | Tests wheter the given entry is exported by the imported interface.
  isExported :: EnvEntry -> Bool
  isExported = flip Set.member (interfaceExports iface) . entryScopedName

  -- | Imports all entries of the interface that have been exported explicitly.
  importExportedEntries :: Environment -> Environment
  importExportedEntries =
    importEntries $ map (qualify . entryName &&& id) exportedEntries

  -- | Imports all hidden entries of the interface.
  importHiddenEntries :: Environment -> Environment
  importHiddenEntries = importEntries $ map (entryName &&& id) hiddenEntries

  exportedEntries, hiddenEntries :: [EnvEntry]
  (exportedEntries, hiddenEntries) =
    partition isExported $ Set.toList $ interfaceEntries iface

  -- | Qualifies the name of an imported entry with the module name.
  qualify :: HS.QName -> HS.QName
  qualify (HS.UnQual name) = HS.Qual modName name
  qualify (HS.Qual _ name) = HS.Qual modName name

-------------------------------------------------------------------------------
-- Inserting entries into the environment                                    --
-------------------------------------------------------------------------------

-- | Inserts an entry into the given environment and associates it with
--   the given name.
addEntry :: HS.QName -> EnvEntry -> Environment -> Environment
addEntry name entry env = addEntry' name entry (envDepth env) env

-- | Like 'addEntry' but has an additional parameter for the 'envDepth' value
--   to record.
addEntry' :: HS.QName -> EnvEntry -> Int -> Environment -> Environment
addEntry' name entry depth env = env
  { envEntries = Map.insertWith
                   (\(es1, d1) (es2, d2) ->
                     if d2 == d1 then (es1 `Set.union` es2, d1) else (es2, d2)
                   )
                   (entryScope entry   , name)
                   (Set.singleton entry, depth)
                   (envEntries env)
  }

-- | Inserts the given type signature into the environment.
defineTypeSig :: HS.QName -> HS.Type -> Environment -> Environment
defineTypeSig name typeExpr env =
  env { envTypeSigs = Map.insert name typeExpr (envTypeSigs env) }

-- | Stores the index of the decreasing argument of a recursive function
--   in the environmen
defineDecArg :: HS.QName -> Int -> Environment -> Environment
defineDecArg name index env =
  env { envDecArgs = Map.insert name index (envDecArgs env) }

-------------------------------------------------------------------------------
-- Looking up entries from the environment                                   --
-------------------------------------------------------------------------------

-- | Looks up the entries that have been associated with the given name in
--   the specified scope of the given environment.
lookupEntries :: Scope -> HS.QName -> Environment -> [EnvEntry]
lookupEntries scope name =
  maybe [] (Set.toList . fst) . Map.lookup (scope, name) . envEntries

-- Like 'lookupEntries' but returns @Nothing@ if the given name is ambigous.
lookupEntry :: Scope -> HS.QName -> Environment -> Maybe EnvEntry
lookupEntry = maybeFromSingleton .:. lookupEntries
 where
  maybeFromSingleton :: [a] -> Maybe a
  maybeFromSingleton [x] = Just x
  maybeFromSingleton _   = Nothing

-- | Tests whether there is an entry with the given name in the current
--   environment that was not inherited from a parent environment.
existsLocalEntry :: Scope -> HS.QName -> Environment -> Bool
existsLocalEntry scope name =
  uncurry (==)
    . (Just . envDepth &&& fmap snd . Map.lookup (scope, name) . envEntries)

-- | Tests whether the given name identifies a function in the given
--   environment.
--
--   Returns @False@ if there is no such function.
isFunction :: HS.QName -> Environment -> Bool
isFunction = maybe False isFuncEntry .: lookupEntry ValueScope

-- | Test whether the variable with the given name is not monadic.
isPureVar :: HS.QName -> Environment -> Bool
isPureVar = maybe False (isVarEntry .&&. entryIsPure) .: lookupEntry ValueScope

-- | Looks up the Coq identifier for a Haskell function, (type)
--   constructor or (type) variable with the given name.
--
--   Returns @Nothing@ if there is no such function, (type/smart) constructor,
--   constructor or (type) variable with the given name.
lookupIdent :: Scope -> HS.QName -> Environment -> Maybe G.Qualid
lookupIdent = fmap entryIdent .:. lookupEntry

-- | Looks up the Coq identifier for the smart constructor of the Haskell
--   constructor with the given name.
--
--   Returns @Nothing@ if there is no such constructor.
lookupSmartIdent :: HS.QName -> Environment -> Maybe G.Qualid
lookupSmartIdent =
  fmap entrySmartIdent . find isConEntry .: lookupEntry ValueScope

-- | Gets a list of Coq identifiers for functions, (type/smart) constructors,
--   (type/fresh) variables that were used in the given environment already.
usedIdents :: Environment -> [G.Qualid]
usedIdents = concatMap (concatMap entryIdents . fst) . Map.elems . envEntries
 where
  entryIdents :: EnvEntry -> [G.Qualid]
  entryIdents entry
    | isConEntry entry = [entryIdent entry, entrySmartIdent entry]
    | otherwise        = [entryIdent entry]

-- | Looks up the location of the declaration with the given name.
lookupSrcSpan :: Scope -> HS.QName -> Environment -> Maybe SrcSpan
lookupSrcSpan = fmap entrySrcSpan .:. lookupEntry

-- | Looks up the type variables used by the type synonym, (smart)
--   constructor or type signature of the function with the given name.
--
--   Returns @Nothing@ if there is no such type synonym, function or (smart)
--   constructor with the given name.
lookupTypeArgs :: Scope -> HS.QName -> Environment -> Maybe [HS.TypeVarIdent]
lookupTypeArgs = fmap entryTypeArgs .:. lookupEntry

-- | Looks up the argument and return types of the function or (smart)
--   constructor with the given name.
--
--   Returns @Nothing@ if there is no such function or (smart) constructor
--   with the given name.
lookupArgTypes :: Scope -> HS.QName -> Environment -> Maybe [Maybe HS.Type]
lookupArgTypes = fmap entryArgTypes .:. lookupEntry

-- | Looks up the return type of the function or (smart) constructor with the
--   given name.
--
--   Returns @Nothing@ if there is no such function or (smart) constructor
--   with the given name or the return type is not known.
lookupReturnType :: Scope -> HS.QName -> Environment -> Maybe HS.Type
lookupReturnType = join . fmap entryReturnType .:. lookupEntry

-- | Looks up the number of arguments expected by the Haskell function
--   or smart constructor with the given name.
--
--   Returns @Nothing@ if there is no such function or (smart) constructor
--   with the given name.
lookupArity :: Scope -> HS.QName -> Environment -> Maybe Int
lookupArity =
  fmap entryArity
    .   find (not . (isVarEntry .||. isTypeVarEntry))
    .:. lookupEntry

-- | Looks up the type the type synonym with the given name is associated with.
--
--   Returns @Nothing@ if there is no such type synonym.
lookupTypeSynonym
  :: HS.QName -> Environment -> Maybe ([HS.TypeVarIdent], HS.Type)
lookupTypeSynonym =
  fmap (entryTypeArgs &&& entryTypeSyn)
    .  find isTypeSynEntry
    .: lookupEntry TypeScope

-- | Looks up the annotated type of a user defined Haskell function with the
--   given name.
--
--   Returns @Nothing@, if there is no such type signature or the entry has
--   been replaced already.
lookupTypeSig :: HS.QName -> Environment -> Maybe HS.Type
lookupTypeSig name = Map.lookup name . envTypeSigs

-- | Tests whether the function with the given name is partial.
--
--   Returns @False@ if there is no such function.
isPartial :: HS.QName -> Environment -> Bool
isPartial =
  maybe False (isFuncEntry .&&. entryIsPartial) .: lookupEntry ValueScope

-- | Looks up the index of the decreasing argument of the recursive function
--   with the given name.
--
--   Returns @Nothing@ if there is no such recursive function.
lookupDecArg :: HS.QName -> Environment -> Maybe Int
lookupDecArg name = Map.lookup name . envDecArgs

-------------------------------------------------------------------------------
-- QuickCheck support                                                        --
-------------------------------------------------------------------------------

-- | Enables the translation of QuickCheck properties.
enableQuickCheck :: Environment -> Environment
enableQuickCheck env = env { envQuickCheckEnabled = True }

-- | Tests whether the translation of QuickCheck properties is enabled
--   in the given environment.
--
--   This flag is usually set to @True@ if there is a @import Test.QuickCheck@
--   declaration.
isQuickCheckEnabled :: Environment -> Bool
isQuickCheckEnabled = envQuickCheckEnabled
