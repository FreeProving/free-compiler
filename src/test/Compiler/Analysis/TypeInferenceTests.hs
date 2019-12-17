module Compiler.Analysis.TypeInferenceTests where

import           Test.Hspec

import           Compiler.Analysis.TypeInference
import           Compiler.Monad.Converter
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Pretty

import           Compiler.Util.Test

-- | Test group for type 'inferExprType' tests.
testTypeInference :: Spec
testTypeInference =
  describe "Compiler.Analysis.TypeInference.inferExprType" $ do
    it "infers the type of integer literals correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "42" `shouldInferType` "Prelude.Integer"
    it "infers the type of predefined constants correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "True" `shouldInferType` "Prelude.Bool"
    it "infers the type of predefined constructors correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType "(42, True)" "(Prelude.Integer, Prelude.Bool)"
    it "infers the type of conditions in if-expressions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType "\\c -> if c then 0 else 1"
                          "Prelude.Bool -> Prelude.Integer"
    it "infers the type of predefined operations correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType
            "(+)"
            "Prelude.Integer -> Prelude.Integer -> Prelude.Integer"
    it "infers the type of partially applied predefined operations correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType "(+) 42" "Prelude.Integer -> Prelude.Integer"
    it "infers the type of polymorphic functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "length" <- defineTestFunc "length" 1 "[a] -> Integer"
          shouldInferType "\\xs ys -> length xs + length ys"
                          "forall a0 a1. [a0] -> [a1] -> Prelude.Integer"
    it "can match hidden and non-hidden types"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType "\\x -> if x then [x, True] else [x, False]"
                          "Prelude.Bool -> [Prelude.Bool]"
    it "infers the type of expressions with type annotation correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "[] :: [Integer]" `shouldInferType` "[Prelude.Integer]"
    it "infers the type of error terms correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "undefined" `shouldInferType` "forall a0. a0"
    it "rejects lists with heterogeneous element types"
      $ shouldReportFatal
      $ fromConverter
      $ do
          inferTestType "[42, True]"

-------------------------------------------------------------------------------
-- Utility functions                                                         --
-------------------------------------------------------------------------------

-- | Parses and infers the type of the given expression.
inferTestType :: String -> Converter HS.TypeSchema
inferTestType input = do
  expr <- parseTestExpr input
  inferExprType expr

-- | Parses and infers the type of the given expression and sets the
--   expectation that the give type is inferred.
shouldInferType :: String -> String -> Converter Expectation
shouldInferType input expectedType = do
  inferredType <- inferTestType input
  return (showPretty inferredType `shouldBe` expectedType)
