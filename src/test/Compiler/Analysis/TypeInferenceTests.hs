module Compiler.Analysis.TypeInferenceTests where

import           Test.Hspec

import           Compiler.Analysis.TypeInference
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

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
    it "infer the type of variables that shadow variables correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType "\\x -> (x, \\x -> x)"
                          "forall a0 a1. a0 -> (a0, a1 -> a1)"
    it "can match types with type synonyms" $ shouldSucceed $ fromConverter $ do
      "Foo" <- defineTestTypeSyn "Foo" [] "[Integer]"
      "[] :: Foo" `shouldInferType` "[Prelude.Integer]"
    it "expands type synonyms when necessary"
      $ shouldSucceed
      $ fromConverter
      $ do
          "Foo"  <- defineTestTypeSyn "Foo" [] "[Integer]"
          "head" <- defineTestFunc "head" 1 "[a] -> a"
          "head ([] :: Foo)" `shouldInferType` "Prelude.Integer"
    it "rejects lists with heterogeneous element types"
      $ shouldReportFatal
      $ fromConverter
      $ do
          inferTestType "[42, True]"

-- | Test group for type 'addTypeAppExprs' tests.
testAddTypeAppExprs :: Spec
testAddTypeAppExprs =
  describe "Compiler.Analysis.TypeInference.addTypeAppExprs" $ do
    it "type arguments of constructors are applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldAddTypeAppExprs "(42, True)"
            $ "Prelude.(,) @Prelude.Integer @Prelude.Bool 42 True"
    it "type arguments of functions are applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "head" <- defineTestFunc "head" 1 "[a] -> a"
          shouldAddTypeAppExprs "head [1]"
            $  "head @Prelude.Integer (Prelude.(:) @Prelude.Integer 1 "
            ++ "(Prelude.([]) @Prelude.Integer))"
    it "does not apply functions shadowed by lambda visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> a"
          "\\f x -> f x" `shouldAddTypeAppExprs` "\\f x -> f x"
    it "does not apply functions shadowed by case visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> a"
          shouldAddTypeAppExprs "case (f, 42) of (f, x) -> f x"
            $  "case Prelude.(,) @(Prelude.Integer -> Prelude.Integer) "
            ++ "                 @Prelude.Integer (f @Prelude.Integer) 42 of {"
            ++ "    Prelude.(,) f x -> f x"
            ++ "  }"

    it "generates distinct fresh type variables in different scopes"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> a"
          shouldAddTypeAppExprs "(\\x -> f x, \\x -> f x)"
            $  "Prelude.(,) @(a@1 -> a@1) @(a@2 -> a@2)"
            ++ "            (\\x -> f @a@1 x) (\\x -> f @a@2 x)"

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
  return (inferredType `prettyShouldBe` expectedType)

addTypeAppTestExprs :: String -> Converter HS.Expr
addTypeAppTestExprs input = do
  expr <- parseTestExpr input
  addTypeAppExprs expr

shouldAddTypeAppExprs :: String -> String -> Converter Expectation
shouldAddTypeAppExprs input expectedOutput = do
  output <- addTypeAppTestExprs input
  return (output `prettyShouldBe` expectedOutput)
