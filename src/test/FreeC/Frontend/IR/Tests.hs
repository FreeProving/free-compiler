-- | This module contains tests for modules with the @FreeC.Frontend.IR@ prefix.
module FreeC.Frontend.IR.Tests ( testIRFrontend ) where

import           Test.Hspec

import           FreeC.Frontend.IR.ParserTests
import           FreeC.Frontend.IR.ScannerTests

-- | Test group for tests of modules with the @FreeC.Frontend.IR@ prefix.
testIRFrontend :: Spec
testIRFrontend = do
  testIRScanner
  testIRParser
