import           Test.Hspec

import           Compiler.Analysis.PartialityAnalysisTests
import           Compiler.Analysis.RecursionAnalysisTests
import           Compiler.Analysis.TypeInferenceTests
import           Compiler.Backend.Coq.ConverterTests
import           Compiler.Environment.RenamerTests
import           Compiler.IR.ReferenceTests
import           Compiler.IR.SubstTests
import           Compiler.IR.SubtermTests
import           Compiler.IR.UnificationTests
import           Compiler.Monad.ReporterTests

-- | Runs all unit tests for the Haskell to Coq compiler.
main :: IO ()
main = hspec $ do
  testReference
  testPartialityAnalysis
  testRecursionAnalysis
  testTypeInference
  testConverter
  testRenamer
  testExprSubst
  testSubterm
  testUnification
  testReporter
