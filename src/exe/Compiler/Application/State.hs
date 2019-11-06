-- | This module contains a data type that encapsulates the state of the
--   application.

module Compiler.Application.State where

import           Compiler.Application.Options

-- | Data type that encapsulates the state of the application.
data AppState = AppState
  { appOpts :: Options
    -- ^ The command line options.
  }

-- | Builds the default state of the application.
makeDefaultAppState :: IO AppState
makeDefaultAppState = do
  defaultOptions <- makeDefaultOptions
  return AppState {appOpts = defaultOptions}

-------------------------------------------------------------------------------
-- Setters                                                                   --
-------------------------------------------------------------------------------

-- | Updates the parsed command line options of the given state.
setOpts :: Options -> AppState -> AppState
setOpts opts state = state { appOpts = opts }
