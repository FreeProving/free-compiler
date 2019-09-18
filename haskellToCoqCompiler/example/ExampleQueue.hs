module ExampleQueue where

import Test.QuickCheck

-------------------------------------------------------------------------------

null :: [a] -> Bool
null xs = case xs of
  []     -> True
  x : xs -> False

not :: Bool -> Bool
not b = case b of
  True  -> False
  False -> True

append :: [a] -> [a] -> [a]
append xs ys = case xs of
  []      -> ys
  x : xs' -> x : (append xs' ys)

reverse :: [a] -> [a]
reverse xs = case xs of
  []      -> []
  x : xs' -> reverse xs' `append` [x]

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

-------------------------------------------------------------------------------

type QueueI a = ([a], [a])

emptyI :: QueueI a
emptyI = ([], [])

isEmptyI :: QueueI a -> Bool
isEmptyI a0
  = case a0 of
        (a1, a2) -> null a1

frontI :: QueueI a -> a
frontI a5
  = case a5 of
        (a6, a7) -> case a6 of
                        a10 : a11 -> a10
                        []        -> undefined

addI :: a -> QueueI a -> QueueI a
addI a14 a15
  = case a15 of
        (a16, a17) -> flipQ (a16, a14 : a17)

flipQ :: QueueI a -> QueueI a
flipQ a20
  = case a20 of
        (a21, a22) -> case a21 of
                          []          -> (reverse a22, [])
                          (:) a25 a26 -> ((:) a25 a26, a22)

-------------------------------------------------------------------------------

invariant :: QueueI a -> Bool
invariant qi = case qi of (f,b) -> null b || not (null f)

-- When translating this property to Coq, we need to manually fix a type error
-- since Coq cannot infer the type of invariant and emptyI.
--     prop_inv_empty :: Bool
--     prop_inv_empty = invariant emptyI

prop_inv_add :: a -> QueueI a -> Property
prop_inv_add x q = invariant q ==> invariant (addI x q)

-------------------------------------------------------------------------------

toQueue :: QueueI a -> Queue a
toQueue qi = case qi of (f,b) -> f `append` reverse b

prop_isEmpty :: QueueI a -> Property
prop_isEmpty qi = invariant qi ==> isEmptyI qi === isEmpty (toQueue qi)

prop_add :: a -> QueueI a -> Property
prop_add x qi = toQueue (addI x qi) === add x (toQueue qi)

prop_front :: QueueI a -> Property
prop_front qi = invariant qi && not (isEmptyI qi) ==> frontI qi === front (toQueue qi)
