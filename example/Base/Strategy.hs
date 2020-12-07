module Base.Strategy where

import           Data.Function   (id)
import           Data.List       (append, sum)
import           Data.Maybe
import           Test.QuickCheck

import           FreeC.NonDet

-------------------------------------------------------------------------------
-- Trivial Test Functions                                                    --
-------------------------------------------------------------------------------

-- The boolean property `True` is always satisfied. However, the equivalent
-- property `id True` cannot be proved because the application of `id`
-- introduces sharing syntax and the QuickCheck extension considers impure
-- values as false.
prop_true :: Bool
prop_true = True

prop_id_true :: Bool
prop_id_true = id True

-------------------------------------------------------------------------------
-- Tracing Test Functions                                                    --
-------------------------------------------------------------------------------
-- Tracing messages in shared expressions are collected twice in a call-by-name
-- setting and once otherwise.
add_traced :: Integer
add_traced = let x = trace "x" 1
             in x + x

prop_add_traced_cbv :: Property
prop_add_traced_cbv = add_traced === trace "x" 2

prop_add_traced_cbn :: Property
prop_add_traced_cbn = add_traced === trace "x" (trace "x" 2)

prop_add_traced_cbneed :: Property
prop_add_traced_cbneed = add_traced === trace "x" 2

-- In a call-by-name setting, shared expressions may be evaluated just once.
or_true_traced :: Bool
or_true_traced = let x = trace "True" True
                 in x || x

prop_or_true_traced_cbv :: Property
prop_or_true_traced_cbv = or_true_traced === trace "True" True

prop_or_true_traced_cbn :: Property
prop_or_true_traced_cbn = or_true_traced === trace "True" True

prop_or_true_traced_cbneed :: Property
prop_or_true_traced_cbneed = or_true_traced === trace "True" True

-- In a call-by-name setting, shared expressions can be evaluated twice.
or_false_traced :: Bool
or_false_traced = let x = trace "False" False
                  in x || x

prop_or_false_traced_cbv :: Property
prop_or_false_traced_cbv = or_false_traced === trace "False" False

prop_or_false_traced_cbn :: Property
prop_or_false_traced_cbn = or_false_traced
  === trace "False" (trace "False" False)

prop_or_false_traced_cbneed :: Property
prop_or_false_traced_cbneed = or_false_traced === trace "False" False

-- In a call-by-value setting, the arguments of non-strict functions are
-- evaluated strictly.
true_or_false_traced :: Bool
true_or_false_traced = trace "True" True || trace "False" False

prop_true_or_false_traced_cbv :: Property
prop_true_or_false_traced_cbv = true_or_false_traced
  === trace "True" (trace "False" True)

prop_true_or_false_traced_cbn :: Property
prop_true_or_false_traced_cbn = true_or_false_traced === trace "True" True

prop_true_or_false_traced_cbneed :: Property
prop_true_or_false_traced_cbneed = true_or_false_traced === trace "True" True

-- Regardless of the evaluation strategy, all arguments are evaluated once if
-- all arguments are needed once.
false_or_true_traced :: Bool
false_or_true_traced = trace "False" False || trace "True" True

prop_false_or_true_traced_cbv :: Property
prop_false_or_true_traced_cbv = false_or_true_traced
  === trace "False" (trace "True" True)

prop_false_or_true_traced_cbn :: Property
prop_false_or_true_traced_cbn = false_or_true_traced
  === trace "False" (trace "True" True)

prop_false_or_true_traced_cbneed :: Property
prop_false_or_true_traced_cbneed = false_or_true_traced
  === trace "False" (trace "True" True)

-- Messages are collected even if a computation fails.
partial_traced :: Integer
partial_traced = trace "1" undefined + trace "2" undefined

prop_partial_traced_cbv :: Property
prop_partial_traced_cbv = partial_traced === trace "1" undefined

prop_partial_traced_cbn :: Property
prop_partial_traced_cbn = partial_traced === trace "1" undefined

prop_partial_traced_cbneed :: Property
prop_partial_traced_cbneed = partial_traced === trace "1" undefined

-------------------------------------------------------------------------------
-- Non-Deterministic Test Functions                                          --
-------------------------------------------------------------------------------
-- In a call-by-name setting, we do not have call-time-choice semantics.
add_non_det :: Integer
add_non_det = let x = 1 ? 2
              in x + x

prop_add_non_det_cbv :: Property
prop_add_non_det_cbv = add_non_det === 2 ? 4

prop_add_non_det_cbn :: Property
prop_add_non_det_cbn = add_non_det === 2 ? 3 ? 3 ? 4

prop_add_non_det_cbneed :: Property
prop_add_non_det_cbneed = add_non_det === 2 ? 4

-- Another example that shows the difference between run-time choice and
-- call-time choice.
or_true_false_non_det :: Bool
or_true_false_non_det = let x = True ? False
                        in x || x

prop_or_true_false_non_det_cbv :: Property
prop_or_true_false_non_det_cbv = or_true_false_non_det === True ? False

prop_or_true_false_non_det_cbn :: Property
prop_or_true_false_non_det_cbn = or_true_false_non_det === True ? True ? False

prop_or_true_false_non_det_cbneed :: Property
prop_or_true_false_non_det_cbneed = or_true_false_non_det === True ? False

-- Partial computations can cancel non-deterministic computations if the
-- right handler is selected for partiality.
partial_non_det :: Integer
partial_non_det = undefined ? 1

prop_partial_non_det_cbv :: Property
prop_partial_non_det_cbv = partial_non_det === undefined

prop_partial_non_det_cbn :: Property
prop_partial_non_det_cbn = partial_non_det === undefined

prop_partial_non_det_cbneed :: Property
prop_partial_non_det_cbneed = partial_non_det === undefined

-------------------------------------------------------------------------------
-- Deep Sharing Test Functions                                               --
-------------------------------------------------------------------------------
-- In the 'add_tracing' and 'add_non_det' examples, sharing is introduced
-- explicitly using a @let@-binding. This example demonstrates, that the
-- arguments of functions are shared automatically.
double :: Integer -> Integer
double x = x + x

prop_double_cbv :: Property
prop_double_cbv = double (trace "x" 1) === trace "x" 2

prop_double_cbn :: Property
prop_double_cbn = double (trace "x" 1) === trace "x" (trace "x" 2)

prop_double_cbneed :: Property
prop_double_cbneed = double (trace "x" 1) === trace "x" 2

-- Since the compiler transforms every application (including constructor
-- applications) into a flat form where all arguments are only variables,
-- sharing is also applied deeply within data structures.
double_maybe :: Maybe Integer -> Maybe Integer
double_maybe Nothing  = Nothing
double_maybe (Just x) = Just (x + x)

prop_double_maybe_cbv :: Property
prop_double_maybe_cbv = double_maybe (trace "mx" (Just (trace "x" 1)))
  === trace "mx" (trace "x" (Just 2))

prop_double_maybe_cbn :: Property
prop_double_maybe_cbn = double_maybe (trace "mx" (Just (trace "x" 1)))
  === trace "mx" (trace "x" (trace "x" (Just 2)))

prop_double_maybe_cbneed :: Property
prop_double_maybe_cbneed = double_maybe (trace "mx" (Just (trace "x" 1)))
  === trace "mx" (trace "x" (Just 2))
