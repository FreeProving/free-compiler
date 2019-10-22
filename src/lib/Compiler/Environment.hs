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
  -- * Inserting entries into the environment
  , addEntry
  , importEntry
  , definePartial
  , defineDecArg
  , defineTypeSig
  -- * Looking up entries from the environment
  , lookupEntry
  , isLocalEntry
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
  , defineProof
  , defineProofs
  , lookupProof
  )
where

import           Data.Composition               ( (.:)
                                                , (.:.)
                                                )
import           Data.List                      ( find )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromMaybe )
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
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
type ScopedName = (Scope, HS.Name)

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
  , envEntries :: Map ScopedName (EnvEntry, Int)
    -- ^ Maps Haskell names to entries for declarations.
    --   In addition to the entry, the 'envDepth' of the environment is
    --   recorded.
  , envTypeSigs :: Map HS.Name HS.Type
    -- ^ Maps names of Haskell functions to their annotated types.
  , envFreshIdentCount :: Map String Int
    -- ^ The number of fresh identifiers that were used in the environment
    --   with a certain prefix.
  , envPartialFuncs :: Set HS.Name
    -- ^ The names of partial functions. This map also contains entries for
    --   functions that have not yet been defined and functions that are
    --   shadowed by local vairables.
  , envDecArgs :: Map HS.Name Int
    -- ^ Maps Haskell function names to the index of their decreasing argument.
    --   Contains no entry for non-recursive functions, but there are also
    --   entries for functions that are shadowed by local variables.
  , envQuickCheckEnabled :: Bool
    -- ^ Whether the translation of QuickCheck properties is enabled in the
    --   current environment (i.e. the module imports @Test.QuickCheck@).
  , envDefinedProofs :: Map HS.Name G.Proof
    -- ^ Proofs for QuickCheck properties that were loaded from the proof
    --   configuration file.
  }
  deriving Show

-- | An environment that does not even contain any predefined types and
--   functions.
emptyEnv :: Environment
emptyEnv = Environment
  { envDepth             = 0
  , envEntries           = Map.empty
  , envFreshIdentCount   = Map.empty
  , envPartialFuncs      = Set.empty
  , envDecArgs           = Map.empty
  , envTypeSigs          = Map.empty
  , envQuickCheckEnabled = False
  , envDefinedProofs     = Map.empty
  }

-- | Creates a child environment of the given environment.
childEnv :: Environment -> Environment
childEnv env = env { envDepth = envDepth env + 1 }

-- | Tests whether the given environment has no parent environment.
isTopLevel :: Environment -> Bool
isTopLevel = (== 0) . envDepth

-------------------------------------------------------------------------------
-- Inserting entries into the environment                                    --
-------------------------------------------------------------------------------

-- | Inserts an entry into the given environment and associates it with
--   the given name.
addEntry :: HS.Name -> EnvEntry -> Environment -> Environment
addEntry name entry env = addEntry' name entry (envDepth env) env

-- | Like 'addEntry' but has an additional parameter for the 'envDepth' value
--   to record.
addEntry' :: HS.Name -> EnvEntry -> Int -> Environment -> Environment
addEntry' name entry depth env = env
  { envEntries = Map.insert (entryScope entry, name)
                            (entry           , depth)
                            (envEntries env)
  }

-- | Inserys an entry into the given environment and associates it with the
--   given name.
importEntry :: HS.Name -> EnvEntry -> Environment -> Environment
importEntry name entry env = addEntry' name entry (-1) env

-- | Inserts the given type signature into the environment.
defineTypeSig :: HS.Name -> HS.Type -> Environment -> Environment
defineTypeSig name typeExpr env =
  env { envTypeSigs = Map.insert name typeExpr (envTypeSigs env) }

-- | Inserts the given function name into the set of partial functions.
definePartial :: HS.Name -> Environment -> Environment
definePartial name env =
  env { envPartialFuncs = Set.insert name (envPartialFuncs env) }

-- | Stores the index of the decreasing argument of a recursive function
--   in the environmen
defineDecArg :: HS.Name -> Int -> Environment -> Environment
defineDecArg name index env =
  env { envDecArgs = Map.insert name index (envDecArgs env) }

-------------------------------------------------------------------------------
-- Looking up entries from the environment                                   --
-------------------------------------------------------------------------------

-- | Looksup the entry with the given name in the specified scope of the
--   given environment.
--
--   Returns @Nothing@ if there is no such entry.
lookupEntry :: Scope -> HS.Name -> Environment -> Maybe EnvEntry
lookupEntry scope name = fmap fst . Map.lookup (scope, name) . envEntries

-- | Tests whether the entry with the given name was declared in the current
--   environment (i.e., was not inherited from a parent environment).
isLocalEntry :: Scope -> HS.Name -> Environment -> Bool
isLocalEntry scope name =
  uncurry (==)
    . (Just . envDepth &&& fmap snd . Map.lookup (scope, name) . envEntries)

-- | Tests whether the given name identifies a function in the given
--   environment.
--
--   Returns @False@ if there is no such function.
isFunction :: HS.Name -> Environment -> Bool
isFunction = fromMaybe False . fmap isFuncEntry .: lookupEntry ValueScope

-- | Test whether the variable with the given name is not monadic.
isPureVar :: HS.Name -> Environment -> Bool
isPureVar =
  fromMaybe False . fmap (isVarEntry .&&. entryIsPure) .: lookupEntry ValueScope

-- | Looks up the Coq identifier for a Haskell function, (type)
--   constructor or (type) variable with the given name.
--
--   Returns @Nothing@ if there is no such function, (type/smart) constructor,
--   constructor or (type) variable with the given name.
lookupIdent :: Scope -> HS.Name -> Environment -> Maybe G.Qualid
lookupIdent = fmap (G.bare . entryIdent) .:. lookupEntry

-- | Looks up the Coq identifier for the smart constructor of the Haskell
--   constructor with the given name.
--
--   Returns @Nothing@ if there is no such constructor.
lookupSmartIdent :: HS.Name -> Environment -> Maybe G.Qualid
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
lookupSrcSpan :: Scope -> HS.Name -> Environment -> Maybe SrcSpan
lookupSrcSpan = fmap entrySrcSpan .:. lookupEntry

-- | Looks up the type variables used by the type synonym, (smart)
--   constructor or type signature of the function with the given name.
--
--   Returns @Nothing@ if there is no such type synonym, function or (smart)
--   constructor with the given name.
lookupTypeArgs :: Scope -> HS.Name -> Environment -> Maybe [HS.TypeVarIdent]
lookupTypeArgs = fmap entryTypeArgs .:. lookupEntry

-- | Looks up the argument and return types of the function or (smart)
--   constructor with the given name.
--
--   Returns @Nothing@ if there is no such function or (smart) constructor
--   with the given name.
lookupArgTypes :: Scope -> HS.Name -> Environment -> Maybe [Maybe HS.Type]
lookupArgTypes = fmap entryArgTypes .:. lookupEntry

-- | Looks up the return type of the function or (smart) constructor with the
--   given name.
--
--   Returns @Nothing@ if there is no such function or (smart) constructor
--   with the given name or the return type is not known.
lookupReturnType :: Scope -> HS.Name -> Environment -> Maybe HS.Type
lookupReturnType = join . fmap entryReturnType .:. lookupEntry

-- | Looks up the number of arguments expected by the Haskell function
--   or smart constructor with the given name.
--
--   Returns @Nothing@ if there is no such function or (smart) constructor
--   with the given name.
lookupArity :: Scope -> HS.Name -> Environment -> Maybe Int
lookupArity =
  fmap entryArity
    .   find (not . (isVarEntry .||. isTypeVarEntry))
    .:. lookupEntry

-- | Looks up the type the type synonym with the given name is associated with.
--
--   Returns @Nothing@ if there is no such type synonym.
lookupTypeSynonym
  :: HS.Name -> Environment -> Maybe ([HS.TypeVarIdent], HS.Type)
lookupTypeSynonym =
  fmap (entryTypeArgs &&& entryTypeSyn)
    .  find isTypeSynEntry
    .: lookupEntry TypeScope

-- | Looks up the annotated type of a user defined Haskell function with the
--   given name.
--
--   Returns @Nothing@, if there is no such type signature or the entry has
--   been replaced already.
lookupTypeSig :: HS.Name -> Environment -> Maybe HS.Type
lookupTypeSig name = Map.lookup name . envTypeSigs

-- | Tests whether the function with the given name is partial.
--
--   Returns @False@ if there is no such function.
isPartial :: HS.Name -> Environment -> Bool
isPartial name = Set.member name . envPartialFuncs

-- | Lookups the index of the decreasing argument of the recursive function
--   with the given name.
--
--   Returns @Nothing@ if there is no such recursive function.
lookupDecArg :: HS.Name -> Environment -> Maybe Int
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

-- | Adds the Coq proof for the QuickCheck property with the given name
--   to the environment.
defineProof :: HS.Name -> G.Proof -> Environment -> Environment
defineProof name proof env =
  env { envDefinedProofs = Map.insert name proof (envDefinedProofs env) }

-- | Adds multiple Coq proofs for QuickCheck properties to the environment.
defineProofs :: Map HS.Name G.Proof -> Environment -> Environment
defineProofs proofs env =
  env { envDefinedProofs = Map.union proofs (envDefinedProofs env) }

-- | Looks up the Coq proof for the QuickCheck property with the given name.
--
--   Returns a "G.blankProof" if there is no proof for the that QuickCheck
--   property.
lookupProof :: HS.Name -> Environment -> G.Proof
lookupProof name = fromMaybe G.blankProof . Map.lookup name . envDefinedProofs
