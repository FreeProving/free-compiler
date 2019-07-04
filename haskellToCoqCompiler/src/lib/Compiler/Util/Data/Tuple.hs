module Compiler.Util.Data.Tuple where

-- | Like 'uncurry' for functions with three arguments.
uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z

-- | Gets the first element of a triple.
fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

-- | Gets the second element of a triple.
snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x

-- | Gets the third element of a triple.
thd3 :: (a, b, c) -> c
thd3 (_, _, x) = x
