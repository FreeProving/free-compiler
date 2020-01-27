module Queue.QueueI where

import           Queue.Util

type QueueI a = ([a],[a])

emptyI :: QueueI a
emptyI = ([], [])

isEmptyI :: QueueI a -> Bool
isEmptyI qi = case qi of
  (f, b) -> null f

frontI :: QueueI a -> a
frontI qi = case qi of
  (f, b) -> case f of
    []       -> error "frontI: empty queue"
    (x : f') -> x

addI :: a -> QueueI a -> QueueI a
addI x qi = case qi of
  (f, b) -> flipQ (f, x : b)

flipQ :: QueueI a -> QueueI a
flipQ qi = case qi of
  (f, b) -> case f of
    []       -> (reverse b, [])
    (x : f') -> (x : f', b)
