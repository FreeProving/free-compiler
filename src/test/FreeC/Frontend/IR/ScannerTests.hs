-- | This module contains tests for "FreeC.Frontend.IR.Scanner".
module FreeC.Frontend.IR.ScannerTests where

import           Test.Hspec                 hiding ( shouldReturn )

import           FreeC.Frontend.IR.Scanner
import           FreeC.Frontend.IR.Token
import           FreeC.IR.SrcSpan
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Reporter

-- | Tokenizes a string for testing purposes.
scanTest :: String -> Reporter [ Token ]
scanTest = fmap (map getToken) . scan . mkSrcFile "<test-input>"

-- | Sets the expectation that 'scan' produces the given token stream for
--   the given input.
shouldScan :: String -> [ Token ] -> Expectation
shouldScan input expectedTokens = scanTest input `shouldReturn` expectedTokens

-- | Test group for "FreeC.Frontend.IR.Scanner" tests.
testIRScanner :: Spec
testIRScanner = describe "FreeC.Frontend.IR.Scanner" $ do
  it "skips single spaces" $ do
    "x y" `shouldScan` [VarIdent "x", VarIdent "y"]
  it "skips multiple spaces" $ do
    "x  y" `shouldScan` [VarIdent "x", VarIdent "y"]
  it "skips newlines" $ do
    "x\ny" `shouldScan` [VarIdent "x", VarIdent "y"]
  it "skips block comments" $ do
    "x{- ... -}y" `shouldScan` [VarIdent "x", VarIdent "y"]
  it "skips nested block comments" $ do
    "x{- ... {- ... -} ... -}y" `shouldScan` [VarIdent "x", VarIdent "y"]
  it "skips line comments" $ do
    "x-- ...\ny" `shouldScan` [VarIdent "x", VarIdent "y"]
  it "skips leading whitespace" $ do
    "  x" `shouldScan` [VarIdent "x"]
  it "skips trailing whitespace" $ do
    "x  " `shouldScan` [VarIdent "x"]
  it "uses longest prefix matching" $ do
    "ifbthenxelsey" `shouldScan` [VarIdent "ifbthenxelsey"]
