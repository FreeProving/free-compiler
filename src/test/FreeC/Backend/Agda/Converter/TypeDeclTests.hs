-- | This module contains tests for "FreeC.Backend.Agda.Converter.TypeDecl".

module FreeC.Backend.Agda.Converter.TypeDeclTests
  ( testConvertDataDecls
  )
where

import           Test.Hspec

import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Parser
import           FreeC.Test.Environment
import           FreeC.Test.Expectations

shouldConvertTypeDeclsTo :: String -> String -> Converter Expectation
shouldConvertTypeDeclsTo inputString expectedOutput = do
  -- _ <- parseTestIR inputString
  -- agdaCode <- convert
  return ("" `shouldBe` expectedOutput)

testConvertDataDecls :: Spec
testConvertDataDecls =
  describe "FreeC.Backend.Agda.Converter.TypeDecl.convertTypeDecl" $ do
    it "translates non-polymorphic, non-recursive data types correctly"
      $ shouldSucceedWith
      $ do
          "Foo"          <- defineTestTypeCon "Foo" 0
          ("bar", "Bar") <- defineTestCon "Bar" 0 "Foo"
          ("baz", "Baz") <- defineTestCon "Baz" 0 "Foo"
          shouldConvertTypeDeclsTo "data Foo = Bar | Baz"
            $  "data Foo (Shape : Set)(Pos : Shape -> Set) : Set where"
            ++ "  bar : Foo Shape Pos"
            ++ "  baz : Foo Shape Pos"
            ++ "pattern bar = Bar"
            ++ "pattern baz = Baz"

