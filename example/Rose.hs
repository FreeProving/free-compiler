-- This example demonstrates the usage of the "decreasing-argument" pragma
-- to annotate the decreasing argument of a function that cannot be identified
-- by our termination checker automatically.
-- See `doc/CustomPragmas/DecreasingArgumentsPragma.md` for details.

module Rose where

map :: (a -> b) -> [a] -> [b]
map f xs = case xs of
  []        -> []
  (x : xs') -> f x : map f xs'

data Rose a = Rose a [Rose a]

{-# HASKELL_TO_COQ mapRose DECREASES ON r #-}
mapRose :: (a -> b) -> Rose a -> Rose b
mapRose f r = case r of
  (Rose x rs) -> Rose (f x) (map (mapRose f) rs)
