module Demo where

import           Debug.Trace
import           Test.QuickCheck

-- Data type
data Tree a = Empty | Node a (Tree a, Tree a)

-- Partial function.
root :: Tree a -> a
root (Node x _) = x

-- Function with sharing.
doubleRoot :: Tree Integer -> Integer
doubleRoot t = root t + root t

-- Traced value.
tracedTree :: Tree Integer
tracedTree = Node (trace "Root" 1) undefined

-- Example Property
prop_double_root_traced :: Property
prop_double_root_traced = doubleRoot tracedTree === trace "Root" 2






















{-

-- Optional

-- traced, partial value
tracedTreeP :: Tree Integer
tracedTreeP = Node (trace "Root" 1)  (error "Error!" [])

prop_double_root_tracedP :: Property
prop_double_root_tracedP = doubleRoot tracedTreeP === root tracedTreeP + root tracedTreeP

-}
