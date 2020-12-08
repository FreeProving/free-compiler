-- | This example demonstrates how to prove properties that involve the
--   sharing and tracing effects.
module Proofs.Tracing where

import           Debug.Trace
import           Test.QuickCheck

double :: Integer -> Integer
double x = trace "double" (x + x)

prop_trace_is_shared :: Property
prop_trace_is_shared = double (trace "x" 21) === trace "double" (trace "x" 42)
