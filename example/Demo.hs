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
doubleRoot t = root t + root t

-- traced value
tracedTree :: Tree Integer
tracedTree = Node (trace "Root" 1)  [Node (trace "Child" 2) []]

-- traced, partial value
tracedTreeP :: Tree Integer
tracedTreeP = Node (trace "Root" 1)  undefined

-- Properties
prop_double_root_traced :: Property
prop_double_root_traced = doubleRoot tracedTree === trace "Root" 2

