{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | This module contains a data type that encapsulates the state of
--   the converter and a state monad which allows the state to be passed
--   implicitly throught the converter.
--
--   There are also utility functions to modify the state and retreive
--   information stored in the state.

module Compiler.Converter.State
  ( -- * Environment
    Environment
  , Scope(..)
  , emptyEnvironment
  , usedIdents
    -- * Freh identifiers
  , freshIdentCount
    -- * Inserting entries into the environment
  , definePartial
  , definePureVar
  , defineDecArg
  , defineTypeSig
  , defineIdent
  , defineArity
    -- * Looking up entries from the environment
  , isFunction
  , isPartial
  , isPureVar
  , lookupDecArg
  , lookupTypeSig
  , lookupIdent
  , lookupArity
    -- * Shortcuts for inserting entries into the environment
  , defineTypeCon
  , defineTypeVar
  , defineCon
  , defineVar
  , defineFunc
    -- * State monad
  , Converter
  , runConverter
  , evalConverter
  , execConverter
    -- * Modifying environments
  , getEnv
  , inEnv
  , putEnv
  , modifyEnv
  , modifyEnv'
  , localEnv
  )
where

import           Control.Monad.Fail
import           Control.Monad.State
import           Data.Composition               ( (.:) )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( isJust )
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set

import qualified Compiler.Language.Coq.AST     as G
import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.Pretty
import           Compiler.Reporter

-------------------------------------------------------------------------------
-- Environment                                                               --
-------------------------------------------------------------------------------

-- | In Haskell type and function names live in separate scopes. Therefore we
--   need to qualify each name stored in the 'Environment' with the scope it
--   is defined in. There is an additional scope for smart constructors such
--   that multiple Coq identifiers can be associated with the same Haskell data
--   constructor name.
data Scope = TypeScope | ConScope | SmartConScope | VarScope
  deriving (Eq, Ord, Show)

-- | Gets a description of the entries in the given scope.
--
--   This pretty instance is used to generate human readable error messages.
instance Pretty Scope where
  pretty TypeScope     = prettyString "type"
  pretty ConScope      = prettyString "data constructor"
  pretty SmartConScope = prettyString "data constructor"
  pretty VarScope      = prettyString "function or variable"

-- | Type that is used by maps in the 'Environment' to qualify Haskell names
--   with the scopes they are defined in.
type ScopedName = (Scope, HS.Name)

-- | Data type that encapsulates the state of the converter.
data Environment = Environment
  { freshIdentCount :: Map String Int
    -- ^ The number of fresh identifiers that were used in the environment
    --   with a certain prefix.
  , partialFunctions :: Set HS.Name
    -- ^ The names of partial functions.This map also contains entries for
    --   functions that have not yet been defined and functions that are
    --   shadowed by local vairables.
  , pureVars :: Set HS.Name
    -- ^ The names of Haskell variables that are not monadic.
  , decArgs :: Map HS.Name Int
    -- ^ Maps Haskell function names to the index of their decreasing argument.
    --   Contains no entry for non-recursive functions, but there are also
    --   entries for functions that are shadowed by local variables.
  , definedTypeSigs :: Map HS.Name HS.Type
    -- ^ Maps Haskell function names to their annotated type. This map also
    --   contains entries for functions that have not yet been defined and
    --   functions that are shadowed by local vairables.
  , definedIdents :: Map ScopedName G.Qualid
    -- ^ Maps Haskell names of defined functions, (type/smart) constructors and
    --  (type) variables to corresponding Coq identifiers.
  , definedArities       :: Map ScopedName Int
    -- ^ Maps Haskell names to the number of (type) arguments expected by the
    --   corresponding function or (type/smart) constructor. There should be
    --   no entry for (type) variables. This allows one to use this map to
    --   distinguish function and variable identifiers.
  }
  deriving Show

-- | An environment that does not even contain any predefined types and
--   functions.
emptyEnvironment :: Environment
emptyEnvironment = Environment
  { freshIdentCount  = Map.empty
  , partialFunctions = Set.empty
  , pureVars         = Set.empty
  , decArgs          = Map.empty
  , definedTypeSigs  = Map.empty
  , definedIdents    = Map.empty
  , definedArities   = Map.empty
  }

-- | Gets a list of Coq identifiers for functions, (type/smart) constructors,
--   (type/fresh) variables that were used in the given environment already.
usedIdents :: Environment -> [G.Qualid]
usedIdents = Map.elems . definedIdents

-------------------------------------------------------------------------------
-- Inserting entries into the environment                                    --
-------------------------------------------------------------------------------

-- | Inserts the given function name into the set of partial functions.
definePartial :: HS.Name -> Environment -> Environment
definePartial name env =
  env { partialFunctions = Set.insert name (partialFunctions env) }

-- | Inserts the given variable name into the set of non-monadic variables.
definePureVar :: HS.Name -> Environment -> Environment
definePureVar name env = env { pureVars = Set.insert name (pureVars env) }

-- | Stores the index of the decreasing argument of a recursive function
--   in the environment.
defineDecArg :: HS.Name -> Int -> Environment -> Environment
defineDecArg name index env =
  env { decArgs = Map.insert name index (decArgs env) }

-- | Associates the name of a Haskell function with it's annoated type.
--
--   If there is an entry associated with the same name already, the entry
--   is overwritten.
--
--   Type signatures are defined after all data type declarations have been
--   defined but before any function declaration is converted. There are no
--   entries for predefined functions.
defineTypeSig :: HS.Name -> HS.Type -> Environment -> Environment
defineTypeSig name typeExpr env =
  env { definedTypeSigs = Map.insert name typeExpr (definedTypeSigs env) }

-- | Associates the name of a Haskell function, (type/smart) constructor or
--   (type) variable with the given Coq identifier.
--
--   If there is an entry associated with the same name in the given scope
--   already, the entry is overwritten.
--
--   All information that is already associated with the identifier is shadowed
--   by this function (e.g. the arity has to be set after the identifier was
--   inserted into the environment, see 'defineArity'). Note that type
--   signatures (see 'defineTypeSig') are never shadowed.
defineIdent :: Scope -> HS.Name -> G.Qualid -> Environment -> Environment
defineIdent scope name ident env = env
  { definedIdents  = Map.insert (scope, name) ident (definedIdents env)
  , definedArities = Map.delete (scope, name) (definedArities env)
  }

-- | Associates the name of a Haskell function or (type/smart) constructor
--   with the number of expected (type) arguments.
--
--   If there is an entry associated with the same name in the given scope
--   already, the entry is overwritten.
--
--   Unlike 'defineIdent' this function does not shadow existing information.
defineArity :: Scope -> HS.Name -> Int -> Environment -> Environment
defineArity scope name arity env =
  env { definedArities = Map.insert (scope, name) arity (definedArities env) }

-------------------------------------------------------------------------------
-- Looking up entries from the environment                                   --
-------------------------------------------------------------------------------

-- | Tests whether the given name identifies a function in the given
--   environment.
--
--   Returns @False@ if there is no such function.
isFunction :: HS.Name -> Environment -> Bool
isFunction = isJust .: lookupArity VarScope

-- | Tests whether the function with the given name is partial.
--
--   Returns @False@ if there is no such function.
isPartial :: HS.Name -> Environment -> Bool
isPartial name = Set.member name . partialFunctions

-- | Test whether the variable with the given name is not monadic.
isPureVar :: HS.Name -> Environment -> Bool
isPureVar name = Set.member name . pureVars

-- | Lookups the index of the decreasing argument of the recursive function
--   with the given name.
--
--   Returns @Nothing@ if there is no such recursive function.
lookupDecArg :: HS.Name -> Environment -> Maybe Int
lookupDecArg name = Map.lookup name . decArgs

-- | Looks up the annotated type of a user defined Haskell function with the
--   given name.
lookupTypeSig :: HS.Name -> Environment -> Maybe HS.Type
lookupTypeSig name = Map.lookup name . definedTypeSigs

-- | Looks up the Coq identifier for a Haskell function, (type/smart)
--   constructor or (type) variable with the given name.
--
--   Returns @Nothing@ if there is no such function, (type/smart) constructor,
--   constructor or (type) variable with the given name.
lookupIdent :: Scope -> HS.Name -> Environment -> Maybe G.Qualid
lookupIdent scope name = Map.lookup (scope, name) . definedIdents

-- | Looks up the number of (type) monadicarguments expected by the given Haskell
--   function or (type/smart) constructor.
--
--   Returns @Nothing@ if there is no such function, (type/smart) constructor,
--   constructor or (type) variable with the given name.
lookupArity :: Scope -> HS.Name -> Environment -> Maybe Int
lookupArity scope name = Map.lookup (scope, name) . definedArities

-------------------------------------------------------------------------------
-- Shortcuts for inserting entries into the environment                      --
-------------------------------------------------------------------------------

-- | Associates the name of a Haskell type constructor with the corresponding
--   Coq identifier in the given environment.
--
--   If a type constructor with the same name exists, the entry is overwritten.
defineTypeCon
  :: HS.Name  -- ^ The Haskell name of the type constructor.
  -> Int      -- ^ The number of expected type arguments.
  -> G.Qualid -- ^ The Coq identifier for the type constructor.
  -> Environment
  -> Environment
defineTypeCon name arity ident =
  defineArity TypeScope name arity . defineIdent TypeScope name ident

-- | Associates the name of a Haskell type variable with the corresponding Coq
--   identifier in the given environment.
--
--   If a type variable with the same name exists, the entry is overwritten.
defineTypeVar :: HS.Name -> G.Qualid -> Environment -> Environment
defineTypeVar = defineIdent TypeScope

-- | Associates the name of a Haskell data constructor with the corresponding
--   Coq identifiers for the constructor and smart constructor in the given
--   environment.
--
--   If a constructor with the same name exists, the entry is overwritten.
defineCon
  :: HS.Name  -- ^ The Haskell name of the constructor.
  -> Int      -- ^ The number of expected arguments.
  -> G.Qualid -- ^ The Coq identifier for the data constructor.
  -> G.Qualid -- ^ The Coq identifier for the smart constructor.
  -> Environment
  -> Environment
defineCon name arity ident smartIdent =
  defineArity ConScope name arity
    . defineArity SmartConScope name arity
    . defineIdent ConScope      name ident
    . defineIdent SmartConScope name smartIdent

-- | Associates the name of a Haskell variable with the corresponding Coq
--   identifier in the given environment.
--
--   If a function or variable with the same name exists, the entry is
--   overwritten.
defineVar
  :: HS.Name    -- ^ The Haskell name of the variable.
  -> G.Qualid   -- ^ The Coq identifier for the variable.
  -> Environment
  -> Environment
defineVar = defineIdent VarScope

-- | Associates the name of a Haskell function with the corresponding Coq
--   identifier in the given environment.
--
--   If a function or variable with the same name exists, the entry is
--   overwritten.
defineFunc
  :: HS.Name  -- ^ The Haskell name of the function.
  -> Int      -- ^ The number of expected arguments.
  -> G.Qualid -- ^ The Coq identifier of the function.
  -> Environment
  -> Environment
defineFunc name arity ident =
  defineArity VarScope name arity . defineIdent VarScope name ident

-------------------------------------------------------------------------------
-- State monad                                                               --
-------------------------------------------------------------------------------

-- | Type synonym for the state monad used by the converter.
--
--   All converter functions usually require the current 'Environment'
--   to perform the conversion. This monad allows these functions to
--   pass the environment around implicitly.
--
--   Additionally the converter can report error messages and warnings to the
--   user if there is a problem while converting.
newtype Converter a = Converter
  { unwrapConverter :: StateT Environment Reporter a
  }
  deriving (Functor, Applicative, Monad, MonadState Environment)

-- | Runs the converter with the given initial environment and
--   returns the converter's result as well as the final environment.
runConverter :: Converter a -> Environment -> Reporter (a, Environment)
runConverter = runStateT . unwrapConverter

-- | Runs the converter with the given initial environment and
--   returns the converter's result.
evalConverter :: Converter a -> Environment -> Reporter a
evalConverter = evalStateT . unwrapConverter

-- | Runs the converter with the given initial environment and
--   returns the final environment.
execConverter :: Converter a -> Environment -> Reporter Environment
execConverter = execStateT . unwrapConverter

-------------------------------------------------------------------------------
-- Modifying environments                                                    --
-------------------------------------------------------------------------------

-- | Gets the current environment.
getEnv :: Converter Environment
getEnv = get

-- | Gets a specific component of the current environment using the given
--   function to extract the value from the environment.
inEnv :: (Environment -> a) -> Converter a
inEnv = gets

-- | Sets the current environment.
putEnv :: Environment -> Converter ()
putEnv = put

-- | Applies the given function to the environment.
modifyEnv :: (Environment -> Environment) -> Converter ()
modifyEnv = modify

-- | Gets a specific component of the current environment
modifyEnv' :: (Environment -> (a, Environment)) -> Converter a
modifyEnv' = state

-- | Runs the given converter and returns its result but discards all
--   modifications to the environment.
localEnv :: Converter a -> Converter a
localEnv converter = do
  env <- getEnv
  x   <- converter
  putEnv env
  return x

-------------------------------------------------------------------------------
-- Reporting in converter                                                    --
-------------------------------------------------------------------------------

-- | Promotes a reporter to a converter that produces the same result and
--   ignores the environment.
--
--   This type class instance allows 'report' and 'reportFatal' to be used
--   directly in @do@-blocks of the 'Converter' monad without explicitly
--   lifting reporters.
instance MonadReporter Converter where
  liftReporter = Converter . lift

-- | Internal errors (e.g. pattern matching failures in @do@-blocks) are
--   cause fatal error messages to be reported.
instance MonadFail Converter where
  fail = reportFatal . Message Nothing Internal
