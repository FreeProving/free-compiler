-- | Test group for tests of modules below "FreeC.Frontend.IR".

module FreeC.Frontend.IR.Tests where

import Test.Hspec

import           FreeC.Frontend.IR.ParserTests
import           FreeC.Frontend.IR.ScannerTests

-- | Test group for tests of modules below "FreeC.Frontend.IR".
testIRFrontend :: Spec
testIRFrontend = do
  testIRScanner
  testIRParser
