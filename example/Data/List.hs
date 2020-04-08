-- This example contains definitions for commonly used list functions from
-- the @Data.List@ module.

module Data.List where

-------------------------------------------------------------------------------
-- Basic functions                                                           --
-------------------------------------------------------------------------------

-- | Append two lists, i.e.,
--
--   > [x1, ..., xm] ++ [y1, ..., yn] == [x1, ..., xm, y1, ..., yn]
--   > [x1, ..., xm] ++ [y1, ...] == [x1, ..., xm, y1, ...]
append :: [a] -> [a] -> [a]
append xs ys = case xs of
  []      -> ys
  x : xs' -> x : append xs' ys

infixr 5 `append`

-- | Extract the first element of a list, which must be non-empty.
head :: [a] -> a
head xs = case xs of
  []      -> error "head: empty list"
  x : xs' -> x

-- | Extract the elements after the 'head' of a list, which must be non-empty.
tail :: [a] -> [a]
tail xs = case xs of
  []      -> error "tail: empty list"
  x : xs' -> xs'

-- | Test whether the list is empty.
null :: [a] -> Bool
null xs = case xs of
  []      -> True
  x : xs' -> False

-- | Returns the length of a list.
length :: [a] -> Integer
length xs = case xs of
  []      -> 0
  x : xs' -> 1 + length xs'

-------------------------------------------------------------------------------
-- List transformations                                                      --
-------------------------------------------------------------------------------

-- | @'map' f xs@ is the list obtained by applying @f@ to each
--   element of @xs@, i.e.,
--
--   > map f [x1, x2, ..., xn] == [f x1, f x2, ..., f xn]
map :: (a -> b) -> [a] -> [b]
map f xs = case xs of
  []      -> []
  x : xs' -> f x : map f xs'

-- | @'reverse' xs@ returns the elements of @xs@ in reverse order.
reverse :: [a] -> [a]
reverse = reverse' []

-- | Version of 'reverse' with accumulator.
reverse' :: [a] -> [a] -> [a]
reverse' acc xs = case xs of
  []      -> acc
  x : xs' -> reverse' (x : acc) xs'

-- | The 'intersperse' function takes an element and a list and
--   intersperses that element between the elements of the list.
--   For example,
--
--   >>> intersperse ',' "abcde"
--   "a,b,c,d,e"
intersperse :: a -> [a] -> [a]
intersperse sep xs = case xs of
  []     -> []
  y : ys -> y : case ys of
    []     -> []
    z : zs -> sep : intersperse sep ys

-------------------------------------------------------------------------------
-- Reducing lists (folds)                                                    --
-------------------------------------------------------------------------------

-- | Left-associative fold of a structure.
--
--   In the case of lists, 'foldl', when applied to a binary operator, a
--   starting value (typically the left-identity of the operator), and a
--   list, reduces the list using the binary operator, from left to right:
--
--   > foldl f z [x1, x2, ..., xn] == (...((z `f` x1) `f` x2) `f`...) `f` xn
foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f e xs = case xs of
  []      -> e
  x : xs' -> foldl f (f e x) xs'

-- | Right-associative fold of a structure.
--
--   In the case of lists, 'foldr', when applied to a binary operator, a
--   starting value (typically the right-identity of the operator), and a
--   list, reduces the list using the binary operator, from right to left:
--
--   > foldr f z [x1, x2, ..., xn] == x1 `f` (x2 `f` ... (xn `f` z)...)
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f e xs = case xs of
  []      -> e
  x : xs' -> x `f` foldr f e xs'

-- | A variant of 'foldr' that has no base case, and thus may only be applied
--   to non-empty structures.
foldr1 :: (a -> a -> a) -> [a] -> a
foldr1 f xs = case xs of
  []      -> error "foldr1: empty list"
  x : xs' -> foldr f x xs'

-------------------------------------------------------------------------------
-- Special folds                                                             --
-------------------------------------------------------------------------------

-- | The concatenation of all the elements of a list of lists.
concat :: [[a]] -> [a]
concat = foldr append []

-- | 'and' returns the conjunction of a list of 'Bool's.
and :: [Bool] -> Bool
and = foldr (&&) True

-- | 'or' returns the disjunction of a container of 'Bool's.
or :: [Bool] -> Bool
or = foldr (||) False

-- | The 'sum' function computes the sum of the numbers of a list.
sum :: [Integer] -> Integer
sum = foldr (+) 0

-- | The 'product' function computes the product of the numbers of a list.
product :: [Integer] -> Integer
product = foldr (*) 1

-- | The largest element of a non-empty list.
maximum :: [Integer] -> Integer
maximum = foldr1 (\a b -> if a >= b then a else b)

-- | The least element of a non-empty list.
minimum :: [Integer] -> Integer
minimum = foldr1 (\a b -> if a <= b then a else b)

-------------------------------------------------------------------------------
-- Zipping and unzipping lists                                               --
-------------------------------------------------------------------------------

-- | 'zip' takes two lists and returns a list of corresponding pairs.
--
--   > zip [1, 2] ['a', 'b'] = [(1, 'a'), (2, 'b')]
--
--   If one input list is short, excess elements of the longer list are
--   discarded:
--
--   > zip [1] ['a', 'b'] = [(1, 'a')]
--   > zip [1, 2] ['a'] = [(1, 'a')]
zip :: [a] -> [b] -> [(a, b)]
zip xs ys = case xs of
  []      -> []
  x : xs' -> case ys of
    []      -> []
    y : ys' -> (x, y) : (zip xs' ys')

-- | 'unzip' transforms a list of pairs into a list of first components and a
--   list of second components.
unzip :: [(a, b)] -> ([a], [b])
unzip xys = case xys of
  []        -> ([], [])
  xy : xys' -> case xy of
    (x, y) -> case unzip xys' of
      (xs, ys) -> (x : xs, y : ys)
