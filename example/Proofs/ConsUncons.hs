-- | This example demonstrates how to use the translation of an error
--   throwing function to prove properties about this function and about the
--   possible errors that can be thrown.
--
--   This example uses an error throwing implementation of the @uncons@
--   function.

module Proofs.ConsUncons where

import           Test.QuickCheck

-- First we have to define the @uncons@ function in an error throwing way.

unconsE :: [a] -> (a, [a])
unconsE ls = case ls of
  []       -> error "uncons: empty list"
  (x : xs) -> (x, xs)

-- Next we can define a simple property about this function, e.g., its relation
-- to the constructor of an non-empty list.

prop_cons_unconsE :: (Eq a, Show a) => a -> [a] -> Property
prop_cons_unconsE x xs = unconsE (x : xs) === (x, xs)
