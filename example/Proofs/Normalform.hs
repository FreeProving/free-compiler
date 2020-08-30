-- | This example defines some data types to check whether the [Normalform]
--   instances are generated correctly.

module Proofs.Normalform where

-- Basic recursive data type
data MyList a = MyNil | MyCons a (MyList a)

-- Mutually recursive data types
data Foo a = Foo (Bar a)
data Bar a = Bar (Foo a) | Baz

-- Data type with 'hidden' recursion
data Tree a = Leaf | Branch a [Tree a]

-- Data type with multiple type vars
data Map k v = Empty | Entry k v (Map k v)
