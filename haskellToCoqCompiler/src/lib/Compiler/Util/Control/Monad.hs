module Compiler.Util.Control.Monad where

-- | Maps each element of a list to a monadic action, evaluates these
--   actions from left to right, and concatenates the resulting lists.
concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = mapM f xs >>= return . concat
