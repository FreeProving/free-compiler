module Compiler.Converter.State
  ( Environment(..)
  , emptyEnvironment
  , define
  , Converter
  , runConverter
  , evalConverter
  , execConverter
  , getEnv
  , inEnv
  , putEnv
  , modifyEnv
  , localEnv
  )
where

import           Control.Monad.State

import           Compiler.Reporter

-------------------------------------------------------------------------------
-- Environment                                                               --
-------------------------------------------------------------------------------

-- | Data type that encapsulates the state of the converter.
data Environment = Environment
  { definedIdents :: [String]
    -- ^ The Coq identifiers for types, (smart) consturctors, functions and
    --   variables that were used for the translation already.
  }

-- | An environment that does not even contain any predefined types and
--   functions.
emptyEnvironment :: Environment
emptyEnvironment = Environment {definedIdents = []}

-- | Adds the given identifier to the list of defined Coq identifiers in the
--   given environment.
define :: String -> Environment -> Environment
define ident env = env { definedIdents = ident : definedIdents env }

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
