{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Compiler.Monad.Application
  ( -- * State monad
    Application
  , runApp
  , reportApp
    -- * Accessing and modifying state
  , getOpts
  , inOpts
  , putOpts
  , modifyOpts
  , modifyOpts'
    -- * Lifting other monads
  , liftReporter
  , liftReporterIO
  , liftConverter
  , liftConverterIO
  )
where

import           Control.Monad.IO.Class
import           Control.Monad.State
import           System.IO                      ( stderr )

import           Compiler.Application.Options
import           Compiler.Environment
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter

-------------------------------------------------------------------------------
-- Application state monad                                                   --
-------------------------------------------------------------------------------

-- | A state monad used by the compiler application to pass the command
--   line options implicitly.
--
--   The entire application is lifted to the 'ConverterIO' monad.
newtype Application a = Application
  { unwrapApplication :: StateT Options ConverterIO a
  }
 deriving (Functor, Applicative, Monad, MonadState Options)

-- | Runs the compiler application.
runApp :: Application a -> IO a
runApp app = do
  defaultOptions <- makeDefaultOptions
  let converter = evalStateT (unwrapApplication app) defaultOptions
      reporter  = evalConverterT converter emptyEnv
  reportToOrExit stderr (reportIOErrors reporter)

-- | Runs the given application and prints the reported messages.
reportApp :: Application a -> Application a
reportApp app = do
  opts <- getOpts
  env  <- liftConverter getEnv
  let converter = runStateT (unwrapApplication app) opts
      reporter  = runConverterT converter env
  ((x, opts'), env') <- liftIO (reportToOrExit stderr (reportIOErrors reporter))
  liftConverter $ putEnv env'
  putOpts opts'
  return x

-------------------------------------------------------------------------------
-- Accessing and modifying state                                             --
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
-- Lifting other monads                                                      --
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

-- | Promotes a 'ReporterIO' to an application that produces the same result
--   and ignores the application's options.
liftReporterIO :: ReporterIO a -> Application a
liftReporterIO = liftConverterIO . lift'

-- | Promotes a 'Converter' to an application that produces the same result
--   and ignores the application's options.
liftConverter :: Converter a -> Application a
liftConverter = liftConverterIO . hoist

-- | Promotes a 'ConverterIO' to an application that produces the same result
--   and ignores the application's options.
liftConverterIO :: ConverterIO a -> Application a
liftConverterIO = Application . lift
