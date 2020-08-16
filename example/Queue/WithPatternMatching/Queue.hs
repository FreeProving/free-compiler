module Queue.WithPatternMatching.Queue where

import           Queue.WithPatternMatching.Util

type Queue a = [ a ]

empty :: Queue a
empty = []

isEmpty :: Queue a -> Bool
isEmpty q = null q

front :: Queue a -> a
front (x : q) = x

add :: a -> Queue a -> Queue a
add x q = q `append` [x]
