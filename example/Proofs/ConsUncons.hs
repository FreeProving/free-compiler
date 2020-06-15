-- | This example demonstrates how to use the translation of an error
--   throwing function to prove properties about this function and about the
--   possible errors that can be thrown.
--
--   This example uses a function @unconsE@ that is an error throwing version
--   of the @uncons@ function.

module Proofs.ConsUncons where

import           Test.QuickCheck

import           Data.List                      ( head )

-- First we have to define the @unconsE@ function in an error throwing way.

unconsE :: [a] -> (a, [a])
unconsE ls = case ls of
  []       -> error "unconsE: empty list"
  (x : xs) -> (x, xs)

-- Next we can define a simple property about this function, e.g., its relation
-- to the constructor of an non-empty list.

prop_cons_unconsE :: (Eq a, Show a) => a -> [a] -> Property
prop_cons_unconsE x xs = unconsE (x : xs) === (x, xs)

-- And we define a property whose validity depends on the concrete effect
-- that is considered in the proof.

fst :: (a, b) -> a
fst p = case p of
  (x, y) -> x

prop_unconsE_fst :: (Eq a, Show a) => [a] -> Property
prop_unconsE_fst xs = fst (unconsE xs) === head xs
