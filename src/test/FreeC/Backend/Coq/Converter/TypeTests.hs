-- | This module contains tests for "FreeC.Backend.Coq.Converter.Type".
module FreeC.Backend.Coq.Converter.TypeTests ( testConvertType ) where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.Type
import           FreeC.Backend.Coq.Pretty         ()
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Expectation setters                                                       --
-------------------------------------------------------------------------------
-- | Parses the given IR type expression, converts it to Coq using
--   'convertType' and sets the expectation that the resulting AST
--   is equal to the given output when pretty printed modulo white
--   space.
shouldConvertTypeTo :: String -> String -> Converter Expectation
shouldConvertTypeTo inputStr expectedOutputStr = do
  input <- parseTestType inputStr
  output <- convertType input
  return (output `prettyShouldBe` expectedOutputStr)

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------
-- | Test group for 'convertType' tests.
testConvertType :: Spec
testConvertType = describe "FreeC.Backend.Coq.Converter.Type.convertType" $ do
  it "converts type variables correctly" $ shouldSucceedWith $ do
    "a" <- defineTestTypeVar "a"
    "a" `shouldConvertTypeTo` "Free Shape Pos a"
  it "converts nullary type constructors correctly" $ shouldSucceedWith $ do
    "Bool" <- defineTestTypeCon "Bool" 0 []
    "Bool" `shouldConvertTypeTo` "Free Shape Pos (Bool Shape Pos)"
  it "converts nullary type constructors correctly" $ shouldSucceedWith $ do
    "Bool" <- defineTestTypeCon "Bool" 0 []
    "Bool" `shouldConvertTypeTo` "Free Shape Pos (Bool Shape Pos)"
  it "converts unary type constructors correctly" $ shouldSucceedWith $ do
    "List" <- defineTestTypeCon "List" 1 []
    "a" <- defineTestTypeVar "a"
    "List a" `shouldConvertTypeTo` "Free Shape Pos (List Shape Pos a)"
  it "converts binary type constructors correctly" $ shouldSucceedWith $ do
    "Pair" <- defineTestTypeCon "Pair" 2 []
    "a" <- defineTestTypeVar "a"
    "b" <- defineTestTypeVar "b"
    "Pair a b" `shouldConvertTypeTo` "Free Shape Pos (Pair Shape Pos a b)"
  it "converts function types correctly" $ shouldSucceedWith $ do
    "a" <- defineTestTypeVar "a"
    "b" <- defineTestTypeVar "b"
    shouldConvertTypeTo "a -> b"
      "Free Shape Pos (Free Shape Pos a -> Free Shape Pos b)"
