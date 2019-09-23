module DemoPartial where

head :: [a] -> a
head xs = case xs of
  []      -> undefined
  x : xs' -> x
