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


null :: List a -> Bool
null list = case list of
  Nil -> True
  Cons _ _ -> False
{-}
--type Queue a = List a
-}
data Test =
  T1 Int
  | T2 String


append :: List a -> List a -> List a
append xs ys  = case xs of
  Nil -> ys
  Cons z zs -> Cons z (append zs ys )

reverse_ :: List a -> List a
reverse_ xs = case xs of
  Nil -> Nil
  Cons y ys -> append (reverse_ ys) (singleton y)

concat_ :: List (List a) -> List a
concat_ xs = case xs of
  Nil -> Nil
  Cons y ys -> append y (concat_ ys)

length' :: List a -> Int
length' xs = case xs of
      Nil -> 0
      Cons y ys -> plus 1 (length' ys)

indexLength :: List a -> Int
indexLength xs = minus (length' xs) 1
