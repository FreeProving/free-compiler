module DemoNestedInduction where

import Prelude hiding (map)
import Test.QuickCheck

data Tree a = Leaf a | Branch (Tree a, Tree a)
  deriving (Eq, Show)

flipTree :: Tree a -> Tree a
flipTree (Leaf a)        = Leaf a
flipTree (Branch (x, y)) = Branch (flipTree y, flipTree x)

prop_flipTree_involutive :: (Show a, Eq a) => Tree a -> Property
prop_flipTree_involutive t = flipTree (flipTree t) === t
