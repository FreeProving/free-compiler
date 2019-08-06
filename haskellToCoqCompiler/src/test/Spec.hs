import           Test.Hspec

import           Compiler.Analysis.PartialityAnalysisTests
import           Compiler.Analysis.RecursionAnalysisTests
import           Compiler.ConverterTests
import           Compiler.Environment.RenamerTests
import           Compiler.Monad.ReporterTests

-- | Runs all unit tests for the Haskell to Coq compiler.
main :: IO ()
main = hspec $ do
  testPartialityAnalysis
  testRecursionAnalysis
  testConverter
  testRenamer
  testReporter
