module DemoQuickCheck where

import Test.QuickCheck

append :: [a] -> [a] -> [a]
append xs ys = case xs of
  []      -> ys
  x : xs' -> x : append xs' ys

prop_append_assoc :: [a] -> [a] -> [a] -> Property
prop_append_assoc xs ys zs =
  (xs `append` ys) `append` zs === xs `append` (ys `append` zs)
