module FastLooseBasic where

import           Test.QuickCheck

data Peano = Zero | S Peano

reverse :: [a] -> [a]
reverse xs = rev [] xs

rev acc []       = acc
rev acc (x : xs) = rev (x : acc) xs

map :: (a -> b) -> [a] -> [b]
map f []       = []
map f (x : xs) = f x : map f xs

comp :: (b -> c) -> (a -> b) -> a -> c
comp g f a = g (f a)

id :: a -> a
id a = a

plus :: Peano -> Peano -> Peano
plus = foldPeano S

minus :: Peano -> Peano -> Peano
minus = foldPeano pred

pred :: Peano -> Peano
pred Zero  = Zero
pred (S n) = n

foldPeano :: (a -> a) -> a -> Peano -> a
foldPeano f a Zero  = a
foldPeano f a (S n) = f (foldPeano f a n)

prop_rev_is_rev_inv :: [a] -> Property
prop_rev_is_rev_inv xs = reverse (reverse xs) === xs
