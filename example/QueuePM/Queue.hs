module QueuePM.Queue where

import           QueuePM.Util

type Queue a = [a]

empty :: Queue a
empty = []

isEmpty :: Queue a -> Bool
isEmpty q = null q

front :: Queue a -> a
front (x : q) = x

add :: a -> Queue a -> Queue a
add x q = q `append` [x]
