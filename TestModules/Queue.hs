module Queue where

data List a =
  Nil
  | Cons a (List a)

null' :: List a -> Bool
null' list = case list of
  Nil -> True
  Cons _ _ -> False

append :: List a -> List a -> List a
append xs ys  = case xs of
  Nil -> ys
  Cons z zs -> Cons z (append zs ys )

singleton :: a -> List a
singleton x = Cons x Nil

type Queue a = List a

empty :: Queue a
empty = Nil

isEmpty :: Queue a -> Bool
isEmpty q = null' q

front :: Queue a -> a
front q = case q of
   Cons x _ -> x

add :: a -> Queue a -> Queue a
add x q = append q (singleton x)
