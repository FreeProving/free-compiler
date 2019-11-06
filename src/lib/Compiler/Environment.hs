-- | This module contains a data type that encapsulates the state of
--   the compiler. There are also utility functions to modify the state and
--   retreive information stored in the state.

module Compiler.Environment
  ( -- * Scope
    Scope(..)
  , entryScope
    -- * Environment
  , Environment(..)
  , emptyEnv
  , childEnv
  , isTopLevel
  -- * Module information
  , makeModuleAvailable
  , lookupAvailableModule
  -- * Import and export entries
  , exportedEntries
  , importEntry
  , importEnv
  , importEnvAs
  -- * Inserting entries into the environment
  , addEntry
  , defineDecArg
  , defineTypeSig
  -- * Looking up entries from the environment
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
import           Data.List                      ( find )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromMaybe )
import           Data.Tuple.Extra               ( (&&&) )
import           Control.Monad                  ( join )

import qualified Compiler.Coq.AST              as G
import           Compiler.Environment.Entry
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Util.Predicate

-------------------------------------------------------------------------------
-- Scope                                                                     --
-------------------------------------------------------------------------------

-- | In Haskell type and function names live in separate scopes. Therefore we
--   need to qualify each name stored in the "Compiler.Environment.Environment"
--   with the scope it is defined in.
data Scope = TypeScope | ValueScope
  deriving (Eq, Ord, Show)

-- | Type that is used by maps in the "Compiler.Environment.Environment" to
--   qualify Haskell names with the scopes they are defined in.
type ScopedName = (Scope, HS.QName)

-- | Gets the scope an entry needs to be defined in.
entryScope :: EnvEntry -> Scope
entryScope DataEntry{}    = TypeScope
entryScope TypeSynEntry{} = TypeScope
entryScope TypeVarEntry{} = TypeScope
entryScope ConEntry{}     = ValueScope
entryScope FuncEntry{}    = ValueScope
entryScope VarEntry{}     = ValueScope

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
  , envAvailableModules :: Map HS.ModName Environment
    -- ^ Maps names of modules that can be imported to their environments.

  , envEntries :: Map ScopedName (EnvEntry, Int)
    -- ^ Maps Haskell names to entries for declarations.
    --   In addition to the entry, the 'envDepth' of the environment is
    --   recorded.
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

-- | Tests whether the given environment has no parent environment.
isTopLevel :: Environment -> Bool
isTopLevel = (== 0) . envDepth

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Inserts the environment of a module with the given name into the
--   environment such that it can be imported.
makeModuleAvailable :: HS.ModName -> Environment -> Environment -> Environment
makeModuleAvailable name modEnv env =
  env { envAvailableModules = Map.insert name modEnv (envAvailableModules env) }

-- | Looks up the environment of another module that can be imported.
lookupAvailableModule :: HS.ModName -> Environment -> Maybe Environment
lookupAvailableModule name = Map.lookup name . envAvailableModules

-------------------------------------------------------------------------------
-- Import and export entries                                                 --
-------------------------------------------------------------------------------

-- | Gets a map of all exported entries by their name.
exportedEntries :: Environment -> Map ScopedName EnvEntry
exportedEntries =
  Map.filterWithKey (flip (const isUnQual))
    . Map.map fst
    . Map.filter ((== 0) . snd)
    . envEntries
 where
  isUnQual :: ScopedName -> Bool
  isUnQual (_, HS.UnQual _) = True
  isUnQual (_, HS.Qual _ _) = False

-- | Inserts an entry into the given environment and associates it with the
--   given name.
--
--   In contrast to 'addEntry' the entry is not added at the current 'envDepth'
--   but at depth @-1@ which indicates that it is not a top level entry but
--   an external entry and should not be exported.
importEntry :: HS.QName -> EnvEntry -> Environment -> Environment
importEntry name entry env = addEntry' name entry (-1) env

-- | Imports all top level entries of the first environment into the
--   second environment.
importEnv :: Environment -> Environment -> Environment
importEnv fromEnv toEnv =
  foldr (uncurry (uncurry (const importEntry))) toEnv
    $ Map.assocs
    $ exportedEntries fromEnv

-- | Like 'importEnv' but all exported entries are qualifed with the given
--   module name.
importEnvAs :: HS.ModName -> Environment -> Environment -> Environment
importEnvAs modName fromEnv toEnv =
  foldr (uncurry (uncurry (const importEntry))) toEnv
    $ Map.assocs
    $ Map.mapKeys (fmap qualify)
    $ exportedEntries fromEnv
 where
  -- | Qualifies the name of an imported entry with the module name.
  qualify :: HS.QName -> HS.QName
  qualify (HS.UnQual name) = HS.Qual modName name
  qualify (HS.Qual _ _) =
    error ("importEnvAs: Cannot import qualified identifiers.")

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
  { envEntries = Map.insert (entryScope entry, name)
                            (entry           , depth)
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

-- | Looksup the entry with the given name in the specified scope of the
--   given environment.
--
--   Returns @Nothing@ if there is no such entry.
lookupEntry :: Scope -> HS.QName -> Environment -> Maybe EnvEntry
lookupEntry scope name = fmap fst . Map.lookup (scope, name) . envEntries

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
isFunction = fromMaybe False . fmap isFuncEntry .: lookupEntry ValueScope

-- | Test whether the variable with the given name is not monadic.
isPureVar :: HS.QName -> Environment -> Bool
isPureVar =
  fromMaybe False . fmap (isVarEntry .&&. entryIsPure) .: lookupEntry ValueScope

-- | Looks up the Coq identifier for a Haskell function, (type)
--   constructor or (type) variable with the given name.
--
--   Returns @Nothing@ if there is no such function, (type/smart) constructor,
--   constructor or (type) variable with the given name.
lookupIdent :: Scope -> HS.QName -> Environment -> Maybe G.Qualid
lookupIdent = fmap (G.bare . entryIdent) .:. lookupEntry

-- | Looks up the Coq identifier for the smart constructor of the Haskell
--   constructor with the given name.
--
--   Returns @Nothing@ if there is no such constructor.
lookupSmartIdent :: HS.QName -> Environment -> Maybe G.Qualid
lookupSmartIdent =
  fmap (G.bare . entrySmartIdent) . find isConEntry .: lookupEntry ValueScope

-- | Gets a list of Coq identifiers for functions, (type/smart) constructors,
--   (type/fresh) variables that were used in the given environment already.
usedIdents :: Environment -> [G.Qualid]
usedIdents = concatMap (entryIdents . fst) . Map.elems . envEntries
 where
  entryIdents :: EnvEntry -> [G.Qualid]
  entryIdents entry
    | isConEntry entry = map G.bare [entryIdent entry, entrySmartIdent entry]
    | otherwise        = map G.bare [entryIdent entry]

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
  fromMaybe False
    .  fmap (isFuncEntry .&&. entryIsPartial)
    .: lookupEntry ValueScope

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
