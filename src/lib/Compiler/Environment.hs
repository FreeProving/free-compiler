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
  -- * Inserting entries into the environment
  , addEntry
  , addEntry'
  , defineDecArg
  , removeDecArg
  -- * Looking up entries from the environment
  , lookupEntries
  , lookupEntry
  , existsLocalEntry
  , refersTo
  , isFunction
  , isVariable
  , isPureVar
  , lookupIdent
  , lookupSmartIdent
  , usedIdents
  , lookupSrcSpan
  , lookupTypeArgs
  , lookupTypeArgArity
  , lookupArgTypes
  , lookupReturnType
  , lookupTypeSchema
  , lookupArity
  , lookupTypeSynonym
  , needsFreeArgs
  , isPartial
  , lookupDecArg
  , lookupDecArgIndex
  , lookupDecArgIdent
  )
where

import           Control.Monad                  ( join )
import           Data.Composition               ( (.:)
                                                , (.:.)
                                                )
import           Data.List                      ( find )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( catMaybes
                                                , isJust
                                                )
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
import           Data.Tuple.Extra               ( (&&&) )

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

-------------------------------------------------------------------------------
-- Environment                                                               --
-------------------------------------------------------------------------------

-- | Data type that encapsulates the state of the converter.
data Environment = Environment
  { envDepth             :: Int
    -- ^ The number of parent environments.

  , envAvailableModules  :: Map HS.ModName ModuleInterface
    -- ^ Maps names of modules that can be imported to their interface.
  , envInSection         :: Bool
    -- ^ Whether the currently converted node is inside of a @Section@
    --   sentence.

  , envEntries           :: Map ScopedName (Set EnvEntry, Int)
    -- ^ Maps Haskell names to entries for declarations.
    --   In addition to the entry, the 'envDepth' of the environment is
    --   recorded.
    --   There can be multiple entries with the same name as long as they are
    --   not referenced. Entries are identified by their original name.
  , envDecArgs           :: Map HS.QName (Int, String)
    -- ^ Maps Haskell function names to the index and name of their decreasing
    --   argument. Contains no entry for non-recursive functions, but there are
    --   also entries for functions that are shadowed by local variables.
  , envFreshIdentCount   :: Map String Int
    -- ^ The number of fresh identifiers that were used in the environment
    --   with a certain prefix.
  }
 deriving Show

-- | An environment that does not even contain any predefined types and
--   functions.
emptyEnv :: Environment
emptyEnv = Environment { envDepth            = 0
                         -- Modules and sections
                       , envAvailableModules = Map.empty
                       , envInSection        = False
                         -- Entries
                       , envEntries          = Map.empty
                       , envDecArgs          = Map.empty
                       , envFreshIdentCount  = Map.empty
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
  { envEntries = Map.insertWith mergeEntries
                                (entryScope entry   , name)
                                (Set.singleton entry, depth)
                                (envEntries env)
  }
 where
  -- | Adds the given set of entries to an existing set of entries.
  --
  --   If the new entries are declared deeper, they shadow the existing
  --   entries, i.e., the resulting set contains the new entries only.
  --   If the new entries are declared at the same depth, they are added
  --   to the existing entries. Both the existing and the new entries
  --   remain visible.
  mergeEntries
    :: (Set EnvEntry, Int) -- ^ The new entries.
    -> (Set EnvEntry, Int) -- ^ The old entries.
    -> (Set EnvEntry, Int)
  mergeEntries (newEntries, newDepth) (oldEntries, oldDepth)
    | newDepth == oldDepth = (newEntries `Set.union` oldEntries, newDepth)
    | otherwise            = (newEntries, newDepth)

-- | Stores the index of the decreasing argument of a recursive function
--   in the environment.
defineDecArg :: HS.QName -> Int -> String -> Environment -> Environment
defineDecArg funcName decArgIndex decArgIdent env = env
  { envDecArgs = Map.insert funcName (decArgIndex, decArgIdent) (envDecArgs env)
  }

-- | Removes the index of the decreasing argument of a recursive function
--   from the environment (e.g., because the function has been transformed
--   into a non-recursive function).
removeDecArg :: HS.QName -> Environment -> Environment
removeDecArg funcName env =
  env { envDecArgs = Map.delete funcName (envDecArgs env) }

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

-- | Tests whether the given name (third argument) refers to an entry with
--   the given original name (first argument).
refersTo :: HS.QName -> Scope -> HS.QName -> Environment -> Bool
refersTo name = maybe False ((== name) . entryName) .:. lookupEntry

-- | Tests whether the given name identifies a function in the given
--   environment.
--
--   Returns @False@ if there is no such function.
isFunction :: HS.QName -> Environment -> Bool
isFunction = maybe False isFuncEntry .: lookupEntry ValueScope

-- | Tests whether the given name identifies a local variable in the given
--   environment.
--
--   Returns @False@ if there is no such variable.
isVariable :: HS.QName -> Environment -> Bool
isVariable = maybe False isVarEntry .: lookupEntry ValueScope

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
lookupTypeArgs =
  fmap entryTypeArgs
    .   find (isTypeSynEntry .||. isConEntry .||. isFuncEntry)
    .:. lookupEntry

-- | Returns the length of the list returned by @lookupTypeArgs@.
lookupTypeArgArity :: Scope -> HS.QName -> Environment -> Maybe Int
lookupTypeArgArity = fmap length .:. lookupTypeArgs

-- | Looks up the argument and return types of the function or (smart)
--   constructor with the given name.
--
--   Returns @Nothing@ if there is no such function or (smart) constructor
--   with the given name.
lookupArgTypes :: Scope -> HS.QName -> Environment -> Maybe [Maybe HS.Type]
lookupArgTypes =
  fmap entryArgTypes . find (isConEntry .||. isFuncEntry) .:. lookupEntry

-- | Looks up the return type of the function or (smart) constructor with the
--   given name.
--
--   Returns @Nothing@ if there is no such function or (smart) constructor
--   with the given name or the return type is not known.
lookupReturnType :: Scope -> HS.QName -> Environment -> Maybe HS.Type
lookupReturnType =
  join
    .   fmap entryReturnType
    .   find (isConEntry .||. isFuncEntry)
    .:. lookupEntry

-- | Gets the type schema of the variable, function or constructor with the
--   given name.
lookupTypeSchema :: Scope -> HS.QName -> Environment -> Maybe HS.TypeSchema
lookupTypeSchema scope name env
  | scope == ValueScope && isVariable name env = do
    typeExpr <- lookupEntry scope name env >>= entryType
    return (HS.TypeSchema NoSrcSpan [] typeExpr)
  | otherwise = do
    typeArgs   <- lookupTypeArgs scope name env
    argTypes   <- lookupArgTypes scope name env
    returnType <- lookupReturnType scope name env
    let typeArgDecls = map (HS.TypeVarDecl NoSrcSpan) typeArgs
        funcType     = HS.funcType NoSrcSpan (catMaybes argTypes) returnType
    return (HS.TypeSchema NoSrcSpan typeArgDecls funcType)

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

-- | Tests whether the function with the given name needs the arguments
--   of the @Free@ monad.
--
--   Returns @False@ if there is no such function.
needsFreeArgs :: HS.QName -> Environment -> Bool
needsFreeArgs =
  maybe False (isFuncEntry .&&. entryNeedsFreeArgs) .: lookupEntry ValueScope

-- | Tests whether the function with the given name is partial.
--
--   Returns @False@ if there is no such function.
isPartial :: HS.QName -> Environment -> Bool
isPartial =
  maybe False (isFuncEntry .&&. entryIsPartial) .: lookupEntry ValueScope

-- | Looks up the index and name of the decreasing argument of the recursive
--   function with the given name.
--
--   Returns @Nothing@ if there is no such recursive function.
lookupDecArg :: HS.QName -> Environment -> Maybe (Int, String)
lookupDecArg name = Map.lookup name . envDecArgs

-- | Like 'lookupDecArg' but returns the decreasing argument's index only.
lookupDecArgIndex :: HS.QName -> Environment -> Maybe Int
lookupDecArgIndex = fmap fst .: lookupDecArg

-- | Like 'lookupDecArg' but returns the decreasing argument's name only.
lookupDecArgIdent :: HS.QName -> Environment -> Maybe String
lookupDecArgIdent = fmap snd .: lookupDecArg
