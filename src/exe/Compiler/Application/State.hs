-- | This module contains a data type that encapsulates the state of the
--   application.

module Compiler.Application.State where

import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map

import           Compiler.Application.Options
import           Compiler.Environment
import qualified Compiler.Haskell.AST          as HS

-- | Data type that encapsulates the state of the application.
data AppState = AppState
  { appOpts :: Options
    -- ^ The command line options.
  , appEnvs :: Map HS.ModName Environment
    -- ^ Environments of compiled or imported modules.
  }

-- | Builds the default state of the application.
makeDefaultAppState :: IO AppState
makeDefaultAppState = do
  defaultOptions <- makeDefaultOptions
  return AppState {appOpts = defaultOptions, appEnvs = Map.empty}

-------------------------------------------------------------------------------
-- Setters                                                                   --
-------------------------------------------------------------------------------

-- | Updates the parsed command line options of the given state.
setOpts :: Options -> AppState -> AppState
setOpts opts state = state { appOpts = opts }

-- | Remembers the environment of a compiled or imported module.
--
--   Existing entries are overwritten.
insertEnv :: HS.ModName -> Environment -> AppState -> AppState
insertEnv name env state =
  state { appEnvs = Map.insert name env (appEnvs state) }

-------------------------------------------------------------------------------
-- Getters                                                                   --
-------------------------------------------------------------------------------

-- | Looks up the environment for the module with the given name.
--
--   Returns @Nothing@ if the module has not been converted or
--   imported before.
lookupEnv :: HS.ModName -> AppState -> Maybe Environment
lookupEnv name = Map.lookup name . appEnvs
