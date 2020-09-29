module Proofs.InductionSchemes where

data MyList a = MyNil | MyCons a (MyList a)

data Tree a   = Forest a (MyList (Tree a))

data MyType a = MyCon (Tree (MyType a))
