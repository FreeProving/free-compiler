module Proofs.Test where

data MyList a =
  MyNil -- No IH
  | MyCons a (MyList a) -- IH for second arg

data MyType a b c =
    My1 a -- No IH
  | My2 (MyType a b c) -- IH
  | My3 [MyType a b c] -- IH
  | My4 [[MyType a b c]] -- No IH
  | My5 (MyList (MyType a b c)) -- No IH

data Tree a = Forest a [Tree a] -- IH for second arg

data Tree2 a = Forest2 (a, [Tree2 a]) -- No IH

type List2 a = [a]

data Tree3 a = Forest3 a (List2 (Tree3 a)) -- IH for second arg
