-- | This module contains tests for modules with the @FreeC.Backend.Coq@ prefix.
module FreeC.Backend.Coq.Tests ( testCoqBackend ) where

import           Test.Hspec

import           FreeC.Backend.Coq.Analysis.ConstantArgumentsTests
import           FreeC.Backend.Coq.Analysis.DecreasingArgumentsTests
import           FreeC.Backend.Coq.ConverterTests

-- | Test group for tests of modules with the @FreeC.Backend.Coq@ prefix.
testCoqBackend :: Spec
testCoqBackend = do
  testConstantArguments
  testConverter
  testDecreasingArguments
