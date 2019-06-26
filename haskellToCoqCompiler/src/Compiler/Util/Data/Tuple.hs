module Compiler.Util.Data.Tuple where

-- | Like 'uncurry' for functions with three arguments.
uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z
