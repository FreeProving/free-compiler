-- | This example demonstrates the experimental pattern matching compiler
--   integration. Compile the module with the @--transform-pattern-matching@
--   command line option.
--
--   Without this option pattern matching on the left-hand side of function
--   declarations and guards would not be supported.
module PatternMatching where

import           Data.Maybe

-------------------------------------------------------------------------------
-- Peano numbers                                                             --
-------------------------------------------------------------------------------
data Peano = Zero | Succ Peano

plus :: Peano -> Peano -> Peano
plus Zero q     = q
plus (Succ p) q = plus p (Succ q)

-------------------------------------------------------------------------------
-- Imported Data Types                                                       --
-------------------------------------------------------------------------------
-- In the following example, the pattern matching compiler knows that the data
-- type @Maybe@ that was imported from @Data.Maybe@ has a constructor @Just@.
alternative :: Maybe a -> Maybe a -> Maybe a
alternative Nothing my = my
alternative mx _       = mx

-------------------------------------------------------------------------------
-- Non-inductively defined functions                                         --
-------------------------------------------------------------------------------
xor :: Bool -> Bool -> Bool
xor True True = False
xor False b   = b
xor b False   = b

zip :: [a] -> [b] -> [(a, b)]
zip [] _              = []
zip _ []              = []
zip (a : as) (b : bs) = (a, b) : zip as bs

-- In the following example, @xs@ is expanded to @y : ys@ on the right-hand
-- side of the third rule by the pattern matching compiler. The result of this
-- substitution is that @intercalate@ does not decrease on its second argument
-- anymore. Even if we add {-# FreeC intercalate DECREASES ON ARGUMENT 2 #-}
-- to bypass our termination checker, Coq's termination checker rejects the
-- generated code.
{-

intercalate :: a -> [a] -> [a]
intercalate _ []       = []
intercalate _ [x]      = [x]
intercalate s (x : xs) = x : s : intercalate s xs

-}
-------------------------------------------------------------------------------
-- Nested patterns                                                           --
-------------------------------------------------------------------------------
unzip :: [(a, b)] -> ([a], [b])
unzip []             = ([], [])
unzip ((x, y) : xys) = case unzip xys of
  (xs, ys) -> (x : xs, y : ys)

-------------------------------------------------------------------------------
-- Guards                                                                    --
-------------------------------------------------------------------------------
max :: Integer -> Integer -> Integer
max n m | n > m = n
        | otherwise = m

data Ordering = LT | EQ | GT

compare :: Integer -> Integer -> Ordering
compare n m | n < m = LT
            | n > m = GT
            | otherwise = EQ
