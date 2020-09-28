-- | This example demonstrates how to use the translation of QuickCheck
--   properties to prove properties like that list concatenation is
--   associative.
--
--   This is an example for an effect-generic proof that involves lemmas.
module Proofs.AppendAssoc where

import           Test.QuickCheck

-- First we have to define list concatenation.
append :: [a] -> [a] -> [a]
append xs ys = case xs of
  []      -> ys
  x : xs' -> x : append xs' ys

infixr 5 `append`

-- Next we state the property that we want to prove, namely that @append@ is
-- associative.
prop_append_assoc :: (Eq a, Show a) => [a] -> [a] -> [a] -> Property
prop_append_assoc xs ys zs
  = xs `append` (ys `append` zs) === (xs `append` ys) `append` zs

-- Proving the property above requires some auxiliary lemmas.
-- The following lemma can be stated using QuickCheck.
prop_append_nil :: (Eq a, Show a) => [a] -> Property
prop_append_nil xs = xs `append` [] === xs
