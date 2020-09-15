-- | Test group for tests of modules below @FreeC.Backend.Coq@.
module FreeC.Backend.Coq.Tests ( testCoqBackend ) where

import           Test.Hspec

import           FreeC.Backend.Coq.Analysis.ConstantArgumentsTests
import           FreeC.Backend.Coq.Analysis.DecreasingArgumentsTests
import           FreeC.Backend.Coq.ConverterTests

-- | Test group for tests of modules below @FreeC.Backend.Coq@.
testCoqBackend :: Spec
testCoqBackend = do
  testConstantArguments
  testConverter
  testDecreasingArguments
