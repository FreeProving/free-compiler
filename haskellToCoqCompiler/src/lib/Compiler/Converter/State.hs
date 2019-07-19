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
    -- * Inserting entries into the environment
  , defineFreshIdent
  , defineIdent
  , defineArity
    -- * Looking up entries from the environment
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
  , localEnv
  )
where

import           Control.Monad.Fail
import           Control.Monad.State
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map

import qualified Compiler.Language.Coq.AST     as G
import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS
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

-- | Type that is used by maps in the 'Environment' to qualify Haskell names
--   with the scopes they are defined in.
type ScopedName = (Scope, HS.Name)

-- | Data type that encapsulates the state of the converter.
data Environment = Environment
  { definedFreshIdents :: [G.Qualid]
    -- ^ The fresh Coq identifiers that were used already.
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
  { definedFreshIdents = []
  , definedIdents      = Map.empty
  , definedArities     = Map.empty
  }

-- | Gets a list of Coq identifiers for functions, (type/smart) constructors,
--   (type/fresh) variables that were used in the given environment already.
usedIdents :: Environment -> [G.Qualid]
usedIdents env = definedFreshIdents env ++ Map.elems (definedIdents env)

-------------------------------------------------------------------------------
-- Inserting entries into the environment                                    --
-------------------------------------------------------------------------------

-- | Adds the given fresh Coq identifier to the given environment.
defineFreshIdent :: G.Qualid -> Environment -> Environment
defineFreshIdent ident env =
  env { definedFreshIdents = ident : definedFreshIdents env }

-- | Associates the name of a Haskell function, (type/smart) constructor or
--   (type) variable with the given Coq identifier.
--
--   If there is an entry associated with the same name in the given scope
--   already, the entry is overwritten.
defineIdent :: Scope -> HS.Name -> G.Qualid -> Environment -> Environment
defineIdent scope name ident env =
  env { definedIdents = Map.insert (scope, name) ident (definedIdents env) }

-- | Associates the name of a Haskell function or (type/smart) constructor
--   with the number of expected (type) arguments.
--
--   If there is an entry associated with the same name in the given scope
--   already, the entry is overwritten.
defineArity :: Scope -> HS.Name -> Int -> Environment -> Environment
defineArity scope name arity env =
  env { definedArities = Map.insert (scope, name) arity (definedArities env) }

-------------------------------------------------------------------------------
-- Looking up entries from the environment                                   --
-------------------------------------------------------------------------------

-- | Looks up the Coq identifier for a Haskell function, (type/smart)
--   constructor or (type) variable with the given name.
--
--   Returns @Nothing@ if there is no such function, (type/smart) constructor,
--   constructor or (type) variable with the given name.
lookupIdent :: Scope -> HS.Name -> Environment -> Maybe G.Qualid
lookupIdent scope name = Map.lookup (scope, name) . definedIdents

-- | Looks up the number of (type) arguments expected by the given Haskell
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
  defineIdent TypeScope name ident . defineArity TypeScope name arity

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
  defineIdent ConScope name ident
  . defineIdent SmartConScope name smartIdent
  . defineArity ConScope name arity
  . defineArity SmartConScope name arity

-- | Associates the name of a Haskell variable with the corresponding Coq
--   identifier in the given environment.
--
--   If a function or variable with the same name exists, the entry is
--   overwritten.
defineVar
  :: HS.Name    -- ^ The Haskell name of the variable.
  -> G.Qualid   -- ^ the Coq identifier for the variable.
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
  defineIdent VarScope name ident
  . defineArity VarScope name arity

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
