module Demo2 where

import           Debug.Trace
import           Test.QuickCheck

-- Recursive function with sharing.
doubleElems :: [Integer] -> Integer
doubleElems []       = 0
doubleElems (x : xs) = x + x + doubleElems xs

prop_double_Elems :: Property
prop_double_Elems = doubleElems [trace "eval 1" 1, trace "eval 2" 2]
  === trace "eval 1" (trace "eval 2" 6)
