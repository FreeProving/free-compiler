import           Test.Hspec

import Compiler.ReporterTests

main :: IO ()
main = hspec $ do
  testReporter
