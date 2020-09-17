-- | This example demonstrates how to prove properties that involve the
--   sharing and tracing effects.

module Proofs.Tracing where

import Debug.Trace
import Test.QuickCheck

foo :: Integer
foo = let x = trace "x" 1 in trace "foo" (x + x)

foo' :: Integer
foo' = trace "foo" (trace "x" 2)

prop_trace_is_shared :: Property
prop_trace_is_shared = foo === foo'
