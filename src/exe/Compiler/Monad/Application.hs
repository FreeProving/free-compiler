{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Compiler.Monad.Application
  ( -- * State monad
    Application
  , runApp
    -- * Accessing and modifying state
  , getState
  , inState
  , putState
  , modifyState
  , modifyState'
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

import           Compiler.Application.State
import           Compiler.Environment
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter

-------------------------------------------------------------------------------
-- Application state monad                                                   --
-------------------------------------------------------------------------------

  -- | A state monad used by the compiler application.
newtype Application a = Application
  { unwrapApplication :: StateT AppState ConverterIO a
  }
 deriving (Functor, Applicative, Monad, MonadState AppState)

-- | Runs the compiler application.
runApp :: Application a -> IO a
runApp app = do
  defaultAppState <- makeDefaultAppState
  let converter = evalStateT (unwrapApplication app) defaultAppState
      reporter  = evalConverterT converter emptyEnv
  reportToOrExit stderr (reportIOErrors reporter)

-------------------------------------------------------------------------------
-- Accessing and modifying state                                             --
-------------------------------------------------------------------------------

-- | Gets the current state of the application.
getState :: Application AppState
getState = get

-- | Gets a specific component of the current state of the application
--   using the given function to extract the value from the state.
inState :: (AppState -> a) -> Application a
inState = gets

-- | Sets the current state of the application.
putState :: AppState -> Application ()
putState = put

-- | Modifies the current state of the application.
modifyState :: (AppState -> AppState) -> Application ()
modifyState = modify

-- | Gets a specific component and modifies the state of the application.
modifyState' :: (AppState -> (a, AppState)) -> Application a
modifyState' = state

-------------------------------------------------------------------------------
-- Lifting other monads                                                      --
-------------------------------------------------------------------------------

-- | IO actions can be embedded into applications.
instance MonadIO Application where
  liftIO = Application . liftIO

-- | Promotes a reporter to an application that produces the same result and
--   ignores the state.
--
--   This type class instance allows 'report' and 'reportFatal' to be used
--   directly in @do@-blocks of the 'Application' monad without explicitly
--   lifting reporters.
instance MonadReporter Application where
  liftReporter = liftConverter . lift'

-- | Promotes a 'ReporterIO' to an application that produces the same result
--   and ignores the state.
liftReporterIO :: ReporterIO a -> Application a
liftReporterIO = liftConverterIO . lift'

-- | Promotes a 'Converter' to an application that produces the same result
--   and ignores the state.
liftConverter :: Converter a -> Application a
liftConverter = liftConverterIO . hoist

-- | Promotes a 'ConverterIO' to an application that produces the same result
--   and ignores the state.
liftConverterIO :: ConverterIO a -> Application a
liftConverterIO = Application . lift
