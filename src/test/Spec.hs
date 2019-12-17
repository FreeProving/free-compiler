import           Test.Hspec

import           Compiler.Analysis.PartialityAnalysisTests
import           Compiler.Analysis.RecursionAnalysisTests
import           Compiler.Analysis.TypeInferenceTests
import           Compiler.ConverterTests
import           Compiler.Environment.RenamerTests
import           Compiler.Haskell.SubstTests
import           Compiler.Haskell.SubtermTests
import           Compiler.Monad.ReporterTests

-- | Runs all unit tests for the Haskell to Coq compiler.
main :: IO ()
main = hspec $ do
  testPartialityAnalysis
  testRecursionAnalysis
  testTypeInference
  testConverter
  testRenamer
  testExprSubst
  testSubterm
  testReporter
