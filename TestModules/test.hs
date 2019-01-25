module Test where
{-
Testfälle für bisherige Funktion des Compilers
-}
data Boolean =
  B_True
  |B_False

data Maybe a =
  Nothing
  | Just a

data Either a b =
  Left a
  | Right b

data Tree a =
  Leaf
  | Branch a (Tree a) (Tree a)



plus :: Int -> Int -> Int
plus a b = a + b

minus :: Int -> Int -> Int
minus a b = a - b

not :: Bool -> Bool
not b = case b of
  False -> True
  True -> False


null :: [a] -> Bool
null list = case list of
  [] -> True
  _ -> False
{-}
--type Queue a = List a
-}
data Test =
  T1 Int
  | T2 String


append :: [a] -> [a] -> [a]
append xs ys  = case xs of
  [] -> ys
  (z : zs) -> z : append zs ys

reverse_ :: [a] -> [a]
reverse_ xs = case xs of
  [] -> []
  (y : ys) -> append (reverse_ ys) (singleton y)

concat_ :: [[a]] -> [a]
concat_ xs = case xs of
  [] -> []
  (y : ys) -> append y (concat_ ys)

length' :: [a] -> Int
length' xs = case xs of
      [] -> 0
      (y : ys) -> plus 1 (length' ys)

indexLength :: [a] -> Int
indexLength xs = minus (length' xs) 1
