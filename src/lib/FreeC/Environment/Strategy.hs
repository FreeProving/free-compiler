-- | This module contains a data type for an evaluation strategy.
--
--   This strategy is decided by the user as an command line option and passed
--   into the environment. It determines how the @share@ operator behaves.
module FreeC.Environment.Strategy where

import           Data.Map.Strict

-- | The data type for an evaluation strategy.
data Strategy = CallByValue | CallByNameOrNeed
 deriving Show

-- | A map of all strategies with their option name as keys.
strategies :: Map String Strategy
strategies = fromList [("cbv", CallByValue), ("cbn", CallByNameOrNeed)]
