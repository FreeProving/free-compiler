module Compiler.Converter.State
  ( Environment
  , emptyEnvironment
  , definedIdents
  , defineTypeCon
  , lookupTypeCon
  , defineTypeVar
  , lookupTypeVar
  , Converter
  , runConverter
  , evalConverter
  , execConverter
  , getEnv
  , inEnv
  , putEnv
  , modifyEnv
  , localEnv
  , liftReporter
  )
where

import           Control.Monad.State
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map

import           Compiler.Language.Coq.AST     as G
import           Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.Reporter

-------------------------------------------------------------------------------
-- Environment                                                               --
-------------------------------------------------------------------------------

-- | Data type that encapsulates the state of the converter.
data Environment = Environment
  { definedTypeCons :: Map HS.Name G.Qualid
    -- ^ Maps Haskell type constructor names to corresponding Coq identifiers.
  , definedTypeVars :: Map HS.Name G.Qualid
    -- ^ Maps Haskell type variable names to corresponding Coq identifiers.
    -- TODO constructor, function and variable names.
  }
  deriving Show

-- | An environment that does not even contain any predefined types and
--   functions.
emptyEnvironment :: Environment
emptyEnvironment =
  Environment {definedTypeCons = Map.empty, definedTypeVars = Map.empty}

-- | Gets a list of Coq identifiers for type constructors and variables,
--   [TODO smart and data consturctors, functions and variables] that were
--   used in the given environment already.
definedIdents :: Environment -> [G.Qualid]
definedIdents env =
  Map.elems (definedTypeCons env) ++ Map.elems (definedTypeVars env)

-- | Associates the name of a Haskell type constructor with the corresponding
--   Coq identifier in the given environment.
--
--   If a type constructor with the same name exists, the entry is overwritten.
defineTypeCon :: HS.Name -> G.Qualid -> Environment -> Environment
defineTypeCon name ident env =
  env { definedTypeCons = Map.insert name ident (definedTypeCons env) }

-- | Looks up the Coq identifier for a Haskell type constructor with the given
--   name in the provided environment.
--
--   Returns @Nothing@ if there is no such type constructor.
lookupTypeCon :: HS.Name -> Environment -> Maybe G.Qualid
lookupTypeCon name = Map.lookup name . definedTypeCons

-- | Associates the name of a Haskell type variable with the corresponding Coq
--   identifier in the given environment.
--
--   If a type variable with the same name exists, the entry is overwritten.
defineTypeVar :: HS.Name -> G.Qualid -> Environment -> Environment
defineTypeVar name ident env =
  env { definedTypeVars = Map.insert name ident (definedTypeVars env) }

-- | Looks up the Coq identifier for a Haskell type variable with the given
--   name in the provided environment.
--
--   Returns @Nothing@ if there is no such type variable.
lookupTypeVar :: HS.Name -> Environment -> Maybe G.Qualid
lookupTypeVar name = Map.lookup name . definedTypeVars

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
type Converter = StateT Environment Reporter

-- | Runs the converter with the given initial environment and
--   returns the converter's result as well as the final environment.
runConverter :: Converter a -> Environment -> Reporter (a, Environment)
runConverter = runStateT

-- | Runs the converter with the given initial environment and
--   returns the converter's result.
evalConverter :: Converter a -> Environment -> Reporter a
evalConverter = evalStateT

-- | Runs the converter with the given initial environment and
--   returns the final environment.
execConverter :: Converter a -> Environment -> Reporter Environment
execConverter = execStateT

-- | Promotes a reporter to a converter that produces the same result and
--   ignores the environment.
liftReporter :: Reporter a -> Converter a
liftReporter = lift

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
