module ExampleQueue1 where

-------------------------------------------------------------------------------
null :: [a] -> Bool
null xs = case xs of
  []     -> True
  x : xs -> False
append :: [a] -> [a] -> [a]
append xs ys = case xs of
  []      -> ys
  x : xs' -> x : (append xs' ys)
-------------------------------------------------------------------------------

type Queue a = [a]

empty :: Queue a
empty = []

isEmpty :: Queue a -> Bool
isEmpty q = null q

front :: Queue a -> a
front a0
  = case a0 of
        a1 : a2 -> a1
        []      -> undefined

add :: a -> Queue a -> Queue a
add x q = q `append` [x]
