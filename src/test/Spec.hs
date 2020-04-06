import           Test.Hspec

import           FreeC.Analysis.RecursionAnalysisTests
import           FreeC.Analysis.TypeInferenceTests
import           FreeC.Backend.Coq.ConverterTests
import           FreeC.Environment.RenamerTests
import           FreeC.Frontend.IR.ParserTests
import           FreeC.Frontend.IR.ScannerTests
import           FreeC.IR.ReferenceTests
import           FreeC.IR.SimilarTests
import           FreeC.IR.SubstTests
import           FreeC.IR.SubtermTests
import           FreeC.IR.UnificationTests
import           FreeC.Monad.ReporterTests
import           FreeC.PipelineTests

-- | Runs all unit tests for the Free Compiler.
main :: IO ()
main = hspec $ do
  testIRScanner
  testIRParser
  testReference
  testPipeline
  testRecursionAnalysis
  testTypeInference
  testConverter
  testRenamer
  testExprSubst
  testSimilar
  testSubterm
  testUnification
  testReporter
