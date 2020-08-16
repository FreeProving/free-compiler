{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | This module contains the state monad used by the compiler's command
--   line interface to pass command line options around implicitly.
module FreeC.Monad.Application
  ( -- * State Monad
    Application
  , runApp
  , reportApp
    -- * Accessing and Modifying State
  , getOpts
  , inOpts
  , putOpts
  , modifyOpts
  , modifyOpts'
    -- * Lifting Other Monads
  , liftReporter
  , liftReporterIO
  , liftConverter
  , liftConverterIO
  ) where

import           Prelude hiding ( fail )

import           Control.Monad.Fail ( MonadFail(..) )
import           Control.Monad.State
  ( MonadIO(..), MonadState(..), MonadTrans(..), StateT(..), evalStateT, get
  , gets, modify, put, state )
import           System.IO ( stderr )

import           FreeC.Application.Options
import           FreeC.Environment
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter

-------------------------------------------------------------------------------
-- Application State Monad                                                   --
-------------------------------------------------------------------------------
-- | A state monad used by the compiler application to pass the command
--   line options implicitly.
--
--   The entire application is lifted to the 'ConverterIO' monad.
newtype Application a
  = Application { unwrapApplication :: StateT Options ConverterIO a }
 deriving ( Functor, Applicative, Monad, MonadState Options )

-- | Runs the compiler application.
runApp :: Application a -> IO a
runApp app = do
  defaultOptions <- makeDefaultOptions
  let converter = evalStateT (unwrapApplication app) defaultOptions
      reporter  = evalConverterT converter emptyEnv
  reportToOrExit stderr reporter

-- | Runs the given application and prints the reported messages.
reportApp :: Application a -> Application a
reportApp app = do
  opts <- getOpts
  env <- getEnv
  let converter = runStateT (unwrapApplication app) opts
      reporter  = runConverterT converter env
  ((x, opts'), env') <- liftIO (reportToOrExit stderr reporter)
  putEnv env'
  putOpts opts'
  return x

-------------------------------------------------------------------------------
-- Accessing and Modifying State                                             --
-------------------------------------------------------------------------------
-- | Gets the options of the application.
getOpts :: Application Options
getOpts = get

-- | Gets a specific component of the the application's options
--   using the given function to extract the value from the 'Options'.
inOpts :: (Options -> a) -> Application a
inOpts = gets

-- | Sets the options of the application.
putOpts :: Options -> Application ()
putOpts = put

-- | Modifies the options of the application.
modifyOpts :: (Options -> Options) -> Application ()
modifyOpts = modify

-- | Gets a specific component and modifies the options of the application.
modifyOpts' :: (Options -> (a, Options)) -> Application a
modifyOpts' = state

-------------------------------------------------------------------------------
-- Lifting Other Monads                                                      --
-------------------------------------------------------------------------------
-- | IO actions can be embedded into applications.
instance MonadIO Application where
  liftIO = Application . liftIO

-- | Promotes a reporter to an application that produces the same result and
--   ignores the application's options.
--
--   This type class instance allows 'report' and 'reportFatal' to be used
--   directly in @do@-blocks of the 'Application' monad without explicitly
--   lifting reporters.
instance MonadReporter Application where
  liftReporter = liftConverter . lift'

-- | Use 'MonadReporter' to lift @fail@ of 'Reporter' to an 'Application'.
instance MonadFail Application where
  fail = liftReporter . fail

-- | Promotes a 'ReporterIO' to an application that produces the same result
--   and ignores the application's options.
liftReporterIO :: ReporterIO a -> Application a
liftReporterIO = liftConverterIO . lift'

-- | Promotes a 'Converter' to an application that produces the same result
--   and ignores the application's options.
instance MonadConverter Application where
  liftConverter = liftConverterIO . hoist

-- | Promotes a 'ConverterIO' to an application that produces the same result
--   and ignores the application's options.
liftConverterIO :: ConverterIO a -> Application a
liftConverterIO = Application . lift
