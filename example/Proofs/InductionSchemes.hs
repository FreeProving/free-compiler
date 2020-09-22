module Proofs.InductionSchemes where

data MyList a = MyNil | MyCons a (MyList a)

data MyPair a b = MyPair a b

data Tree a b = Forest (MyPair a (MyList (Tree a b)))

data AltList a b = AltNil | AltCons a (AltList b a)

type MapEntry k v = MyPair k v

type MapList k v = MyList (MapEntry k v)

data Map k v = Map (MapList k v)

data Foo a = Foo a (Bar a)

data Bar a = Bar a (Foo a)