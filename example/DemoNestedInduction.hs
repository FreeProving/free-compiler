module DemoNestedInduction where

import Prelude hiding (map)
import Test.QuickCheck

data Tree a = Leaf a | Branch (Tree a, Tree a)
  deriving (Eq, Show)

{-# FreeC flipTree DECREASES ON l #-}
flipTree :: Tree a -> Tree a
flipTree l = case l of
                  (Leaf a)        -> Leaf a
                  (Branch (x, y)) -> Branch (flipTree y, flipTree x)

prop_flipTree_involutive :: (Show a, Eq a) => Tree a -> Property
prop_flipTree_involutive t = flipTree (flipTree t) === t
