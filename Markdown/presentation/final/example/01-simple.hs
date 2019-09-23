module DemoSimple where

null :: [a] -> Bool
null xs = case xs of
  []      -> True
  x : xs' -> False
