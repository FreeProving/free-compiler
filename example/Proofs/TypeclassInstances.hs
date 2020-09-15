-- | This example defines some data types to check whether the [Normalform]
--   and [ShareableArgs] instances are generated correctly.
module Proofs.TypeclassInstances where

-- Prelude head function
head :: [a] -> a
head (x : _) = x

-- Basic recursive data type
data MyList a = MyNil | MyCons a (MyList a)

-- Custom head function
myHead :: MyList a -> a
myHead (MyCons x _) = x

-- Mutually recursive data types
data Foo a = Foo (Bar a)

data Bar a = Bar (Foo a) | Baz

-- Data type with 'hidden' recursion
data Tree a = Leaf | Branch a [Tree a]

-- The root of a non-empty tree
root :: Tree a -> a
root (Branch x _) = x

-- The root of the leftmost child of a tree with a non-empty leftmost child
headRoot :: Tree a -> a
headRoot (Branch _ ts) = root (head ts)

-- Data type with multiple type vars
data Map k v = Empty | Entry k v (Map k v)

-- The first entry of a non-empty map
firstMapEntry :: Map k v -> v
firstMapEntry (Entry _ v _) = v

-- A function that shares a data structure, transforms
-- it into a Bool twice and connects the results with a
-- disjunction.
doubleDisjunction :: a -> (a -> Bool) -> Bool
doubleDisjunction x f = let y = x
                        in f y || f y

-- doubleDisjunction specialized for MyList
doubleDisjunctionHead :: MyList Bool -> Bool
doubleDisjunctionHead l = doubleDisjunction l myHead

-- doubleDisjunction specialized for Tree
doubleDisjunctionRoot :: Tree Bool -> Bool
doubleDisjunctionRoot t = doubleDisjunction t root

-- doubleDisjunction specialized for Tree
doubleDisjunctionHeadRoot :: Tree Bool -> Bool
doubleDisjunctionHeadRoot t = doubleDisjunction t headRoot

-- doubleDisjunction specialized for Map
doubleDisjunctionMap :: Map Bool Bool -> Bool
doubleDisjunctionMap m = doubleDisjunction m firstMapEntry

-- Additional data types to check that the generated
-- instances are valid Coq code
--Types with potential name conflict
data T a = TCons a

data T_ = T_Cons

-- Type with nested recursion and type variable instantiation
data Rose a = Rose (Rose Integer, Rose a)

-- Mutually recursive types with nested recursion and type variable
-- instantiation
data A a = ConsA [B Bool] | AVal a

data B a = ConsB [A Bool] | BVal a

-- Indirect recursion hidden in a type synonym
type IntGatherings = MyList (Gathering Integer)

data Gathering a = Many IntGatherings | Single a
