{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | This module a state monad which allows the compiler's state (see
--   "Comiler.Environment") to be passed implicitly throught the converter.
--
--   There are also utility functions to modify the state and retreive
--   information stored in the state.

module Compiler.Monad.Converter
  ( -- * State monad
    Converter
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

import           Compiler.Environment
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Reporter

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
  putEnv (env { envLocalSrcSpans = envLocalSrcSpans emptyEnvironment })
  x <- converter
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
  fail = reportFatal . Message NoSrcSpan Internal
