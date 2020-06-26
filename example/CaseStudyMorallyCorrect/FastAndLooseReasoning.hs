module FastLooseBasic where

import           Test.QuickCheck

data Peano = Zero | S Peano

append :: [a] -> [a] -> [a]
append []       ys = ys
append (x : xs) ys = x : (append xs ys)

reverseNaive :: [a] -> [a]
reverseNaive []       = []
reverseNaive (x : xs) = append (reverseNaive xs) [x]

reverse :: [a] -> [a]
reverse xs = rev xs []

rev []       acc = acc
rev (x : xs) acc = rev xs (x : acc)

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

prop_reverse_is_reverseNaive :: [a] -> Property
prop_reverse_is_reverseNaive xs = reverse xs === reverseNaive xs

prop_rev_is_rev_inv :: [a] -> Property
prop_rev_is_rev_inv xs = reverse (reverse xs) === xs
