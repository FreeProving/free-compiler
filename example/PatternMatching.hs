-- | This example demonstrates the experimental pattern matching compiler
--   integration. Compile the module with the @--transform-pattern-matching@
--   command line option.
--
--   Without this option pattern matching on the left-hand side of function
--   declarations and guards would not be supported.
module PatternMatching where

-------------------------------------------------------------------------------
-- Peano numbers                                                             --
-------------------------------------------------------------------------------
data Peano = Zero | Succ Peano

plus :: Peano -> Peano -> Peano
plus Zero q     = q
plus (Succ p) q = plus p (Succ q)

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

-- In the following example the second rule cannot be replaced by
-- @intercalate _ [x] = [x]@. The pattern matching compiler would
-- generate invalid code in this case.
-- However, the real problem with this example is, that @xs@ in the
-- third rule is expanded to @y : ys@ on the right-hand side. The
-- result of this substitution is that @intercalate@ does not decrease
-- on its second argument anymore.
-- Even if we add {-# FreeC intercalate DECREASES ON ARGUMENT 2 #-}
-- to bypass out termination checker, Coq's termination checker rejects the
-- generated code.
{-

intercalate :: a -> [a] -> [a]
intercalate _ []       = []
intercalate _ (x : []) = [x]
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
-- The following two functions cannot be translated at the moment, because the
-- pattern matching compiler generates @let@ expressions when eliminating guards
-- but our compiler does not support local declarations.
{-

max :: Integer -> Integer -> Integer
max n m | n > m     = n
        | otherwise = m

data Ordering = LT | EQ | GT

compare :: Integer -> Integer -> Ordering
compare n m | n < m     = LT
            | n > m     = GT
            | otherwise = EQ

-}
