module Demo where

import Debug.Trace
import Test.QuickCheck

-- data type
data Tree a = Empty | Node a [Tree a]

-- partial function
root :: Tree a -> a
root (Node x _) = x

-- sharing
doubleRoot :: Tree Integer -> Integer
doubleRoot l = let l' = l in root l' + root l'

-- traced, partial value

tracedTree :: Tree Integer
tracedTree = Node (trace "Root" 1)  [Node (trace "Child" 2) []]

tracedTree' :: Integer
tracedTree' = let t = Node (trace "Root" 1)  [Node (trace "Child" 2) []] in root t  + root t

-- property
prop_double_root_traced :: Property
prop_double_root_traced = doubleRoot tracedTree === trace "Root" 2


