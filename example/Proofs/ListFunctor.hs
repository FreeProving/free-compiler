-- | This example demonstrates how to use the translation of QuickCheck
--   properties to prove properties like that lists fulfill the functor
--   identity law.
--
--   This is an example for a simple effect-generic proof.
module Proofs.ListFunctor where

import           Data.Function   ( id )
import           Data.List       ( map )
import           Test.QuickCheck

prop_map_id :: Property
prop_map_id = map id === id
-- This example does not actually work in GHCi since we are comparing
-- functions. If you still want to test this example, use the following
-- non-point-free definition instead.
{-

import           Prelude                 hiding ( id , map )

prop_map_id :: (Eq a, Show a) => [a] -> Property
prop_map_id xs = map id xs === id xs

-}
