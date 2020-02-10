module Compiler.Analysis.TypeInferenceTests where

import           Test.Hspec

import           Control.Monad.Extra            ( zipWithM_ )

import           Compiler.Analysis.TypeInference
import           Compiler.Environment.Resolver
import           Compiler.Converter.Module      ( defineTypeSigDecl )
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

import           Compiler.Util.Test

-- | Test group for type inference tests.
testTypeInference :: Spec
testTypeInference = do
  testInferExprType
  testInferFuncDeclTypes

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

testInferFuncDeclTypes :: Spec
testInferFuncDeclTypes =
  describe "Compiler.Analysis.TypeInference.inferFuncDeclTypes" $ do
    it "infers the type of non-recursive functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferFuncDeclTypes
            [ "null xs = case xs of {"
              ++ "    [] -> True;"
              ++ "    x : xs' -> False"
              ++ "  }"
            ]
            ["forall t0. [t0] -> Prelude.Bool"]
    it "infers the type of recursive functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferFuncDeclTypes
            [ "length xs = case xs of {"
              ++ "    [] -> 0;"
              ++ "    x : xs' -> 1 + length xs'"
              ++ "  }"
            ]
            ["forall t0. [t0] -> Prelude.Integer"]
    it "infers the type of partial functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferFuncDeclTypes
            [ "head xs = case xs of {"
              ++ "    [] -> error \"head: empty list\";"
              ++ "    x : xs' -> x"
              ++ "  }"
            ]
            ["forall t0. [t0] -> t0"]
    it "uses type variables from the type signature"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferFuncDeclTypes
            [ "foldr :: (a -> b -> b) -> b -> [a] -> b"
            , "foldr f e xs = case xs of {"
            ++ "    [] -> e;"
            ++ "    x : xs' -> f x (foldr f e xs')"
            ++ "  }"
            ]
            ["forall a b. (a -> b -> b) -> b -> [a] -> b"]
    it "abstracted type variable names don't conflict with user defined names"
      $ shouldSucceed
      $ fromConverter
      $ do
          "null"   <- defineTestFunc "null" 1 "[a] -> Bool"
          "append" <- defineTestFunc "append" 2 "[a] -> [a] -> [a]"
          shouldInferFuncDeclTypes
            ["constTrue :: t0 -> Bool", "constTrue x = null ([] `append` [])"]
            ["forall t0 t1. t0 -> Prelude.Bool"]
    it "allows type signaturs to make the type more specific"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferFuncDeclTypes
            [ "intHead :: [Integer] -> Integer"
            , "intHead xs = case xs of {"
            ++ "    [] -> error \"intHead: empty list\";"
            ++ "    x : xs' -> x"
            ++ "  }"
            ]
            ["[Prelude.Integer] -> Prelude.Integer"]

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Test group for type 'inferExprType' tests.
testInferExprType :: Spec
testInferExprType =
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
                          "forall t0 t1. [t0] -> [t1] -> Prelude.Integer"
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
          "undefined" `shouldInferType` "forall t0. t0"
    it "infer the type of variables that shadow variables correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType "\\x -> (x, \\x -> x)"
                          "forall t0 t1. t0 -> (t0, t1 -> t1)"
    it "can match types with type synonyms" $ shouldSucceed $ fromConverter $ do
      "Foo" <- defineTestTypeSyn "Foo" [] "[Integer]"
      "[] :: Foo" `shouldInferType` "Foo"
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
    it "type arguments of 'undefined' are applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldAddTypeAppExprs "True || undefined"
            $ "(||) True (undefined @Prelude.Bool)"
    it "type arguments of 'error \"...\"' are applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldAddTypeAppExprs "False && error \"...\""
            $ "(&&) False (error @Prelude.Bool \"...\")"
    it "type arguments of constructor patterns are not applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> [a]"
          shouldAddTypeAppExprs "case f 42 of { [] -> (); (x : xs) -> () }"
            $  "case f @Prelude.Integer 42 of {"
            ++ "    Prelude.([]) -> Prelude.();"
            ++ "    Prelude.(:) x xs -> Prelude.()"
            ++ "  }"
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
            $  "Prelude.(,) @(t0 -> t0) @(t1 -> t1)"
            ++ "            (\\x -> f @t0 x) (\\x -> f @t1 x)"

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
  inferredType  <- inferTestType input
  inferredType' <- resolveTypes inferredType
  return (inferredType' `prettyShouldBe` expectedType)

-- | Parses the given declarations, adds the type signatures to the environment
--   and infers the types of the function declarations.
--
--   There must be no type declarations. The function declarations should form
--   a single strongly connected component of the dependency graph.
--
--   Returns the types of the function declarations in order of their
--   declaration.
inferTestFuncDeclTypes :: [String] -> Converter [HS.TypeSchema]
inferTestFuncDeclTypes input = localEnv $ do
  ([], typeSigs, funcDecls) <- parseTestDecls input
  mapM_ defineTypeSigDecl typeSigs
  inferFuncDeclTypes funcDecls

-- | Parses the given function declarations, infers its type schema and sets
--   the expectation that the given type schemas are inferred.
shouldInferFuncDeclTypes :: [String] -> [String] -> Converter Expectation
shouldInferFuncDeclTypes input expectedTypes = do
  inferredTypes <- inferTestFuncDeclTypes input
  inferredTypes' <- mapM resolveTypes inferredTypes
  return (zipWithM_ prettyShouldBe inferredTypes' expectedTypes)

-- | Parses the given expression and adds 'HS.TypeAppExpr' nodes to all
--   function and constructor applications for the type arguments of the
--   invoked function or constructor.
addTypeAppTestExprs :: String -> Converter HS.Expr
addTypeAppTestExprs input = do
  expr <- parseTestExpr input
  addTypeAppExprs expr

-- | Parses the given expression, adds 'HS.TypeAppExpr' nodes and sets the
--   expectation that the given expression is obtained.
shouldAddTypeAppExprs :: String -> String -> Converter Expectation
shouldAddTypeAppExprs input expectedOutput = do
  output <- addTypeAppTestExprs input
  output' <- resolveTypes output
  return (output' `prettyShouldBe` expectedOutput)
