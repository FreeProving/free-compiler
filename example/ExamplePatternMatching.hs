module ExamplePatternMatching where

-------------------------------------------------------------------------------

null :: [a] -> Bool
null [] = True
null _  = False

not :: Bool -> Bool
not True  = False
not False = True

append :: [a] -> [a] -> [a]
append []        ys = ys
append (x : xs') ys = x : (append xs' ys)

reverse :: [a] -> [a]
reverse []        = []
reverse (x : xs') = reverse xs' `append` [x]

-------------------------------------------------------------------------------

type Queue a = [a]
--
empty :: Queue a
empty = []

isEmpty :: Queue a -> Bool
isEmpty q = null q

front :: Queue a -> a
front (x : q) = x

add :: a -> Queue a -> Queue a
add x q = q `append` [x]

-------------------------------------------------------------------------------

type QueueI a = ([a],[a])
--
emptyI :: QueueI a
emptyI = ([], [])

isEmptyI :: QueueI a -> Bool
isEmptyI (f, b) = null f

frontI :: QueueI a -> a
frontI (x : f, b) = x

addI :: a -> QueueI a -> QueueI a
addI x (f, b) = flipQ (f, x : b)

flipQ :: QueueI a -> QueueI a
flipQ ([], b) = (reverse b, [])
flipQ q       = q
