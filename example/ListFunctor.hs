-- | This example demonstrates how to use the translation of QuickCheck
--   properties to prove properties like that lists fulfill the functor
--   law.

module ListFunctor where

import Test.QuickCheck

import           Data.Function                  ( id )
import           Data.List                      ( map )

prop_map_id :: Property
prop_map_id = map id === id
