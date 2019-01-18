module Queue where

data List a =
  Nil
  | Cons a (List a)

type Queue a = List a
