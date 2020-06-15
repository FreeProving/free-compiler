-- | This module contains tests for "FreeC.Pass.EtaConversionPass".

module FreeC.Pass.EtaConversionPassTests where

import           Test.Hspec

import           FreeC.Pass.EtaConversionPass
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Parser
import           FreeC.Test.Environment
import           FreeC.Test.Expectations

-------------------------------------------------------------------------------
-- Expectation setters                                                       --
-------------------------------------------------------------------------------

-- | Parses the given expressions, applies the eta conversion
--   pass and sets the expectation that the resulting expression
--   is 'FreeC.IR.Similar.similar' to the expected output.
shouldEtaConvert :: String -> String -> Converter Expectation
shouldEtaConvert inputStr expectedOutputStr = do
  input          <- parseTestExpr inputStr
  expectedOutput <- parseTestExpr expectedOutputStr
  output         <- etaConvertExpr input
  return (output `shouldBeSimilarTo` expectedOutput)

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'etaConversionPass' tests.
testEtaConversionPass :: Spec
testEtaConversionPass = describe "FreeC.Pass.EtaConversionPass" $ do
  it "leaves fully applied functions unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestFunc "f" 2 "Foo -> Foo -> Foo"
    "f x y" `shouldEtaConvert` "f x y"
  it "leaves over applied functions unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestFunc "f" 2 "Foo -> Foo -> Foo"
    "f x y z" `shouldEtaConvert` "f x y z"
  it "eta-converts under applied functions" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestFunc "f" 2 "Foo -> Foo -> Foo"
    "f x" `shouldEtaConvert` "\\y -> f x y"
  it "leaves application of local variables unchanged" $ shouldSucceedWith $ do
    "\\(f :: a -> b -> c) x -> f x"
      `shouldEtaConvert` "\\(f :: a -> b -> c) x -> f x"
  it "leaves fully applied constructors unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestTypeCon "Bar" 0 ["Bar"]
    _ <- defineTestCon "Bar" 2 "Foo -> Foo -> Bar"
    "Bar x y" `shouldEtaConvert` "Bar x y"
  it "leaves over applied functions unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestTypeCon "Bar" 0 ["Bar"]
    _ <- defineTestCon "Bar" 2 "Foo -> Foo -> Bar"
    "Bar x y z" `shouldEtaConvert` "Bar x y z"
  it "eta-converts under applied functions" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestTypeCon "Bar" 0 ["Bar"]
    _ <- defineTestCon "Bar" 2 "Foo -> Foo -> Bar"
    "Bar x" `shouldEtaConvert` "\\y -> Bar x y"
