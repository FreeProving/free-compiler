-- This example contains definitions for commonly used tuple functions from
-- the @Data.Tuple@ module.
module Data.Tuple where

-- | Extract the first component of a pair.
fst :: (a, b) -> a
fst (x, _) = x

-- | Extract the second component of a pair.
snd :: (a, b) -> b
snd (_, y) = y

-- | Converts an uncurried function to a curried function.
curry :: ((a, b) -> c) -> a -> b -> c
curry f x y = f (x, y)

-- | Converts a curried function to a function on pairs.
uncurry :: (a -> b -> c) -> ((a, b) -> c)
uncurry f p = f (fst p) (snd p)

-- | Swaps the components of a pair.
swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)
