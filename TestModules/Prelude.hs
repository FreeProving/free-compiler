module Prelude where

data Bool = True1 | False1

and :: Bool -> Bool -> Bool
and b1 b2 = case b1 of
  False -> False
  True -> case b2 of
        False -> False
        True -> True

or :: Bool -> Bool -> Bool
or b1 b2 = case b1 of
  True -> True
  False -> case b2 of
      True -> True
      False -> False

not :: Bool -> Bool
not b = case b of
  True -> False
  False -> True

otherwise :: Bool
otherwise = True
