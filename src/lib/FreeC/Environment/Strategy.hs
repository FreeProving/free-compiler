-- | This module contains a data type for an evaluation strategy.
--
--   This strategy is decided by the user as an command line option and passed
--   into the environment. It determines how the @share@ operator behaves.
module FreeC.Environment.Strategy where

import           Data.List       ( intercalate )
import           Data.Map.Strict ( Map, fromList )

-- | The data type for an evaluation strategy.
data Strategy = CallByValue | CallByName | CallByNeed
 deriving Show

-- | The option value, name and strategy of call-by-value.
callByValue :: (String, String, Strategy)
callByValue = ("cbv", "call-by-value", CallByValue)

-- | The option value, name and strategy of call-by-name.
callByName :: (String, String, Strategy)
callByName = ("cbn", "call-by-name", CallByName)

-- | The option value, name and strategy of call-by-need.
callByNeed :: (String, String, Strategy)
callByNeed = ("cbneed", "call-by-need", CallByNeed)

-- | A list of all strategies.
strategies :: [(String, String, Strategy)]
strategies = [callByValue, callByName, callByNeed]

-- | The option value of the default strategy.
defaultStrategy :: String
defaultStrategy = let (opt, _, _) = callByNeed
                  in opt

-- | Show all strategies with their option value and name.
showStrategies :: String
showStrategies = intercalate ", "
  $ map (\(opt, name, _) -> "`" ++ opt ++ "`(" ++ name ++ ")") strategies

-- | A map of all strategies with their option as keys.
strategyMap :: Map String Strategy
strategyMap = fromList $ [(opt, strat) | (opt, _, strat) <- strategies]
