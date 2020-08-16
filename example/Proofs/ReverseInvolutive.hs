module Proofs.ReverseInvolutive where

-- @reverse@ is not yet part of our @Prelude@ but of Haskell's @Prelude@.
-- Thus, we have to hide @reverse@ if we want to run this test in GHCi.
import           Prelude         hiding ( reverse )

import           Test.QuickCheck

-- First we have to define @reverse@.
-- We are using an inefficient version of @reverse@ using @append@.
-- Feel free to replace this with an accumulator version and adapt the proofs.
append :: [ a ] -> [ a ] -> [ a ]
append xs ys = case xs of
  []      -> ys
  x : xs' -> x : append xs' ys

infixr 5 `append`

reverse :: [ a ] -> [ a ]
reverse xs = case xs of
  []     -> []
  x : xs -> reverse xs `append` [x]

-- Next we state the property that we want to prove, namely that @reverse@ is
-- its own inverse.
prop_reverse_involutive :: (Eq a, Show a) => [ a ] -> Property
prop_reverse_involutive xs = reverse (reverse xs) === xs

-- For the proof that @reverse@ is not involutive in a partial setting,
-- consider the following counterexample.
reverse_involutive_counterexample :: [ () ]
reverse_involutive_counterexample = () : undefined

-- For the proof that @reverse@ is involutive in a total setting, we need
-- the following lemmas.
prop_reverse_append_singleton :: (Eq a, Show a) => [ a ] -> a -> Property
prop_reverse_append_singleton xs x = reverse (xs `append` [x]) === x
  : reverse xs
