-- This example demonstrates the usage of the decreasing argument pragma
-- to annotate the decreasing argument of a function that cannot be identified
-- by our termination checker automatically.
-- See @doc\/CustomPragmas\/DecreasingArgumentPragma.md@ for details.
module DecreasingArgumentsPragma where

import           Data.List ( map )

data Rose a = Rose a [Rose a]

{-# FreeC mapRose DECREASES ON r #-}
mapRose :: (a -> b) -> Rose a -> Rose b
mapRose f r = case r of
  Rose x rs -> Rose (f x) (map (mapRose f) rs)

{-# FreeC mapRose' DECREASES ON ARGUMENT 2 #-}
mapRose' :: (a -> b) -> Rose a -> Rose b
mapRose' f (Rose x rs) = Rose (f x) (map (mapRose' f) rs)
