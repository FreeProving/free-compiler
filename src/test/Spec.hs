-- | This is the main module of the compiler's test suite.

module Spec where

import           Test.Hspec

import           FreeC.Backend.Coq.Tests
import           FreeC.Environment.RenamerTests
import           FreeC.Frontend.IR.Tests
import           FreeC.IR.Tests
import           FreeC.Monad.ReporterTests
import           FreeC.PipelineTests

-- | Runs all unit tests for the Free Compiler.
main :: IO ()
main = hspec $ do
  testIR
  testIRFrontend
  testCoqBackend

  testPipeline
  testRenamer

  testReporter
