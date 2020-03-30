import           Test.Hspec

import           FreeC.Analysis.RecursionAnalysisTests
import           FreeC.Analysis.TypeInferenceTests
import           FreeC.Backend.Coq.ConverterTests
import           FreeC.Environment.RenamerTests
import           FreeC.IR.ReferenceTests
import           FreeC.IR.SubstTests
import           FreeC.IR.SubtermTests
import           FreeC.IR.UnificationTests
import           FreeC.Monad.ReporterTests
import           FreeC.Pass.PartialityAnalysisPassTests

-- | Runs all unit tests for the Free Compiler.
main :: IO ()
main = hspec $ do
  testReference
  testPartialityAnalysisPass
  testRecursionAnalysis
  testTypeInference
  testConverter
  testRenamer
  testExprSubst
  testSubterm
  testUnification
  testReporter
