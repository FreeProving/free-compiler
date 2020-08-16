-- | This module contains tests for "FreeC.Environment".
module FreeC.EnvironmentTests where

import           Test.Hspec

import           FreeC.Environment.FreshTests
import           FreeC.Environment.RenamerTests

-- | Test group
testEnvironment :: Spec
testEnvironment = do
  testFreshIdentifiers
  testRenamer
