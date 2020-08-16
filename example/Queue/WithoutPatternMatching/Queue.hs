module Queue.WithoutPatternMatching.Queue where

import           Queue.WithoutPatternMatching.Util

type Queue a = [ a ]

empty :: Queue a
empty = []

isEmpty :: Queue a -> Bool
isEmpty q = null q

front :: Queue a -> a
front q = case q of
  []     -> error "front: empty queue"
  x : q' -> x

add :: a -> Queue a -> Queue a
add x q = q `append` [x]
