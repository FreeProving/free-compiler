module Test where
{-
Testfälle für bisherige Funktion des Compilers
-}


plus :: Int -> Int -> Int
plus a b = a + b


not :: Bool -> Bool
not b = case b of
  False -> True
  True -> False

--null :: List a -> Bool
--null list = case list of
  --Nil -> True
  --Cons _ _ -> False

--type Queue a = List a

append :: List a -> List a -> List a
append xs ys = case xs of
  Nil -> ys
  Cons z zs -> Cons z (append zs ys)

data Bool = True
        | False

data Maybe a = Nothing
              | Just a

data Either a b =
  Left a
  | Right b

data List a = Nil
            | Cons a (List a)

data Tree a =
  Leaf
  | Branch a (Tree a) (Tree a)
