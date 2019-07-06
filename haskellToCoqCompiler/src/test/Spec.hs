import           Test.Hspec

import           Compiler.Converter.RenamerTests
import           Compiler.ReporterTests

-- | Runs all unit tests for the Haskell to Coq compiler.
main :: IO ()
main = hspec $ do
  testRenamer
  testReporter
