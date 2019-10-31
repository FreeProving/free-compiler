module ExampleQueue.QueueI where

import           ExampleQueue.Util

type QueueI a = ([a], [a])

emptyI :: QueueI a
emptyI = ([], [])

isEmptyI :: QueueI a -> Bool
isEmptyI a0 = case a0 of
  (a1, a2) -> null a1

frontI :: QueueI a -> a
frontI a5 = case a5 of
  (a6, a7) -> case a6 of
    a10 : a11 -> a10
    []        -> undefined

addI :: a -> QueueI a -> QueueI a
addI a14 a15 = case a15 of
  (a16, a17) -> flipQ (a16, a14 : a17)

flipQ :: QueueI a -> QueueI a
flipQ a20 = case a20 of
  (a21, a22) -> case a21 of
    []        -> (reverse a22, [])
    a25 : a26 -> (a25 : a26, a22)
