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
  input          <- parseTestFuncDecl inputStr
  expectedOutput <- parseTestFuncDecl expectedOutputStr
  output         <- etaConvertFuncDecl input
  return (output `shouldBeSimilarTo` expectedOutput)

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'etaConversionPass' tests.  
testEtaConversionPass :: Spec
testEtaConversionPass = describe "FreeC.Pass.EtaConversionPass" $ do
  it
      "applies functions under-applied on the top-level to their missing arguments"
    $ shouldSucceedWith
    $ do
        _ <- defineTestTypeCon "Foo" 0
        _ <- defineTestFunc "f" 1 "Foo -> Foo -> Foo"
        _ <- defineTestFunc "g" 2 "Foo -> Foo -> Foo"
        "f = g x" `shouldEtaConvert` "f (y :: Foo) :: Foo = g x y"

-- These are the old tests, but since the testing interface has changed
-- and we now test whole function declarations instead of right-hand sides,
-- these tests don't work anymore.
-- I'll leave them here for reference for now, but they should be removed later.
{-
  it "leaves fully applied functions unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0
    _ <- defineTestFunc "f" 2 "Foo -> Foo -> Foo"
    "f x y" `shouldEtaConvert` "f x y"
  it "leaves over applied functions unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0
    _ <- defineTestFunc "f" 2 "Foo -> Foo -> Foo"
    "f x y z" `shouldEtaConvert` "f x y z"
  it "eta-converts under applied functions" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0
    _ <- defineTestFunc "f" 2 "Foo -> Foo -> Foo"
    "f x" `shouldEtaConvert` "\\y -> f x y"
  it "leaves application of local variables unchanged" $ shouldSucceedWith $ do
    "\\(f :: a -> b -> c) x -> f x"
      `shouldEtaConvert` "\\(f :: a -> b -> c) x -> f x"
  it "leaves fully applied constructors unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0
    _ <- defineTestTypeCon "Bar" 0
    _ <- defineTestCon "Bar" 2 "Foo -> Foo -> Bar"
    "Bar x y" `shouldEtaConvert` "Bar x y"
  it "leaves over applied functions unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0
    _ <- defineTestTypeCon "Bar" 0
    _ <- defineTestCon "Bar" 2 "Foo -> Foo -> Bar"
    "Bar x y z" `shouldEtaConvert` "Bar x y z"
  it "eta-converts under applied functions" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0
    _ <- defineTestTypeCon "Bar" 0
    _ <- defineTestCon "Bar" 2 "Foo -> Foo -> Bar"
    "Bar x" `shouldEtaConvert` "\\y -> Bar x y"
        -}
