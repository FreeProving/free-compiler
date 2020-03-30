-- | This example demonstrates the experimental pattern matching compiler
--   integration. Compile the module with the `--transform-pattern-matching`
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
plus Zero     q = q
plus (Succ p) q = plus p (Succ q)

-------------------------------------------------------------------------------
-- Non-inductively defined functions                                         --
-------------------------------------------------------------------------------

xor :: Bool -> Bool -> Bool
xor True  True  = False
xor False b     = b
xor b     False = b

zip :: [a] -> [b] -> [(a, b)]
zip []       bs       = []
zip as       []       = []
zip (a : as) (b : bs) = (a, b) : zip as bs

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
