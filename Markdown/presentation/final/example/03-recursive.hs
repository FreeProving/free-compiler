module DemoRecursive where

append :: [a] -> [a] -> [a]
append xs ys = case xs of
  []      -> ys
  x : xs' -> x : append xs' ys
