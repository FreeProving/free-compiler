module FreeC.Frontend.IR.ScannerTests where

import           Test.Hspec

import           FreeC.Frontend.IR.Scanner
import           FreeC.Frontend.IR.Token
import           FreeC.IR.SrcSpan
import           FreeC.Util.Test

-- | Sets the expectation that 'scan' produces the given token stream for
--   the given input.
shouldScan :: String -> [Token] -> Expectation
shouldScan input expectedTokens = shouldSucceed $ do
  tokens <- scan (mkSrcFile "test-input" input)
  return (map getToken tokens `shouldBe` expectedTokens)

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
  it "skips leading white space" $ do
    "  x" `shouldScan` [VarIdent "x"]
  it "skips trailing white space" $ do
    "x  " `shouldScan` [VarIdent "x"]
  it "uses longest prefix matching" $ do
    "ifbthenxelsey" `shouldScan` [VarIdent "ifbthenxelsey"]
