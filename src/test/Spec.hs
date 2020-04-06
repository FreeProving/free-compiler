import           Test.Hspec

import           FreeC.Analysis.RecursionAnalysisTests
import           FreeC.Analysis.TypeInferenceTests
import           FreeC.Backend.Coq.ConverterTests
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

  testPipeline
  testTypeInference
  testRenamer

  testConverter
  testRecursionAnalysis

  testReporter
