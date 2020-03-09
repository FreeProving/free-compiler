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
  testAnnotateExprTypes
  testInferFuncDeclTypes
  testAnnotateFuncDeclTypes

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Test group for type 'inferFuncDeclTypes' tests.
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
    it "infers the type of functions with vanishing type arguments correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestFunc "eq" 2 "a -> a -> Bool"
          shouldInferFuncDeclTypes
            [ "length xs = case xs of {"
              ++ "    []      -> if [] `eq` [] then 0 else 1;"
              ++ "    x : xs' -> 1 + length xs'"
              ++ "  }"
            ]
            ["forall t0 t1. [t0] -> Prelude.Integer"]
    it
        "infers the type of functions that depend on functions with vanishing type arguments correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestFunc "true" 0 "forall a. Bool"
          shouldInferFuncDeclTypes ["zero = if true && true then 0 else 1"]
                                   ["forall t0 t1. Prelude.Integer"]
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

-- | Test group for type 'annotateFuncDeclTypes' tests.
testAnnotateFuncDeclTypes :: Spec
testAnnotateFuncDeclTypes =
  describe "Compiler.Analysis.TypeInference.annotateFuncDeclTypes" $ do
    it "annotates the types of simple functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldAnnotateFuncDeclTypes
            ["null xs = case xs of { [] -> True; x : xs' -> False }"]
            [ "null (xs :: [t0]) = (case xs of {"
              ++ "    Prelude.([]) -> True;"
              ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) -> False"
              ++ "  }) :: Prelude.Bool"
            ]
    it "annotates the types of recursive functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldAnnotateFuncDeclTypes
            ["length xs = case xs of { [] -> 0; x : xs' -> 1 + length xs' }"]
            [ "length (xs :: [t0]) = (case xs of {"
              ++ "    Prelude.([]) -> 0;"
              ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) ->"
              ++ "      (+) 1 (length @t0 xs')"
              ++ "  }) :: Prelude.Integer"
            ]
    it "annotates vanishing type arguments correctly in non-recursive functions"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestFunc "true" 0 "forall a. Bool"
          shouldAnnotateFuncDeclTypes
            ["zero = if true && true then 0 else 1"]
            [ "zero = (if (&&) (true @t0) (true @t1) then 0 else 1)"
                ++ "  :: Prelude.Integer"
            ]
    it "annotates vanishing type arguments correctly in recursive functions"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestFunc "eq" 2 "a -> a -> Bool"
          shouldAnnotateFuncDeclTypes
            [ "length xs = case xs of {"
              ++ "    []      -> if [] `eq` [] then 0 else 1;"
              ++ "    x : xs' -> 1 + length xs'"
              ++ "  }"
            ]
            [ "length (xs :: [t0]) = (case xs of {"
              ++ "    Prelude.([]) ->"
              ++ "      if eq @[t1] (Prelude.([]) @t1) (Prelude.([]) @t1)"
              ++ "        then 0"
              ++ "        else 1;"
              ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) ->"
              ++ "      (+) 1 (length @t0 @t1 xs')"
              ++ "  }) :: Prelude.Integer"
            ]
    it
        "annotates vanishing type arguments correctly in mutually recursive functions"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestFunc "eq" 2 "a -> a -> Bool"
          shouldAnnotateFuncDeclTypes
            [ "length xs = case xs of {"
            ++ "    []      -> if [] `eq` [] then 0 else 1;"
            ++ "    x : xs' -> 1 + length' xs'"
            ++ "  }"
            , "length' xs = case xs of {"
            ++ "    []      -> if [] `eq` [] then 0 else 1;"
            ++ "    x : xs' -> 1 + length xs'"
            ++ "  }"
            ]
            [ "length (xs :: [t0]) = (case xs of {"
            ++ "    Prelude.([]) ->"
            ++ "      if eq @[t1] (Prelude.([]) @t1) (Prelude.([]) @t1)"
            ++ "        then 0"
            ++ "        else 1;"
            ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) ->"
            ++ "      (+) 1 (length' @t0 @t1 @t2 xs')"
            ++ "  }) :: Prelude.Integer"
            , "length' (xs :: [t0]) = (case xs of {"
            ++ "    Prelude.([]) ->"
            ++ "      if eq @[t2] (Prelude.([]) @t2) (Prelude.([]) @t2)"
            ++ "        then 0"
            ++ "        else 1;"
            ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) ->"
            ++ "      (+) 1 (length @t0 @t1 @t2 xs')"
            ++ "  }) :: Prelude.Integer"
            ]
    it "handels qualified identifiers correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestTypeCon "Tree" 1
          _ <- defineTestCon "Leaf" 1 "a -> Tree a"
          _ <- defineTestCon "Fork" 2 "Tree a -> Tree a -> Tree a"
          enterTestModule "M"
          shouldAnnotateFuncDeclTypes
            [ "size t = case t of {"
              ++ "    Leaf x -> 1;"
              ++ "    Fork l r -> size l + M.size r"
              ++ "  }"
            ]
            [ "size (t :: Tree t0) = (case t of {"
              ++ "    Leaf (x :: t0) -> 1;"
              ++ "    Fork (l :: Tree t0) (r :: Tree t0)"
              ++ "      -> (+) (size @t0 l) (M.size @t0 r)"
              ++ "  }) :: Prelude.Integer"
            ]
    it "annotates the types of partial functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldAnnotateFuncDeclTypes
            ["head xs = case xs of { [] -> undefined; x : xs' -> x }"]
            [ "head (xs :: [t0]) = (case xs of {"
              ++ "    Prelude.([]) -> undefined @t0;"
              ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) -> x"
              ++ "  }) :: t0"
            ]

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

-- | Test group for type 'annotateExprTypes' tests.
testAnnotateExprTypes :: Spec
testAnnotateExprTypes =
  describe "Compiler.Analysis.TypeInference.annotateExprTypes" $ do
    it "type arguments of constructors are applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldAnnotateExprTypes "(42, True)"
            $ "Prelude.(,) @Prelude.Integer @Prelude.Bool 42 True"
    it "type arguments of functions are applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "head" <- defineTestFunc "head" 1 "[a] -> a"
          shouldAnnotateExprTypes "head [1]"
            $  "head @Prelude.Integer (Prelude.(:) @Prelude.Integer 1 "
            ++ "(Prelude.([]) @Prelude.Integer))"
    it "type arguments of 'undefined' are applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldAnnotateExprTypes "True || undefined"
            $ "(||) True (undefined @Prelude.Bool)"
    it "type arguments of 'error \"...\"' are applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldAnnotateExprTypes "False && error \"...\""
            $ "(&&) False (error @Prelude.Bool \"...\")"
    it "type arguments of constructor patterns are not applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> [a]"
          shouldAnnotateExprTypes "case f 42 of { [] -> (); (x : xs) -> () }"
            $  "case f @Prelude.Integer 42 of {"
            ++ "    Prelude.([]) -> Prelude.();"
            ++ "    Prelude.(:) (x :: Prelude.Integer)"
            ++ "                (xs :: [Prelude.Integer])"
            ++ "      -> Prelude.()"
            ++ "  }"
    it "does not apply functions shadowed by lambda visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> a"
          shouldAnnotateExprTypes "\\f x -> f x"
                                  "\\(f :: t0 -> t1) (x :: t0) -> f x"
    it "does not apply functions shadowed by case visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> a"
          shouldAnnotateExprTypes "case (f, 42) of (f, x) -> f x"
            $  "case Prelude.(,) @(Prelude.Integer -> Prelude.Integer) "
            ++ "                 @Prelude.Integer (f @Prelude.Integer) 42 of {"
            ++ "    Prelude.(,) (f :: Prelude.Integer -> Prelude.Integer)"
            ++ "                (x :: Prelude.Integer) -> f x"
            ++ "  }"
    it "generates distinct fresh type variables in different scopes"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> a"
          shouldAnnotateExprTypes "(\\x -> f x, \\x -> f x)"
            $  "Prelude.(,) @(t0 -> t0) @(t1 -> t1)"
            ++ "            (\\(x :: t0) -> f @t0 x)"
            ++ "            (\\(x :: t1) -> f @t1 x)"

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
  inferredTypes  <- inferTestFuncDeclTypes input
  inferredTypes' <- mapM resolveTypes inferredTypes
  return (zipWithM_ prettyShouldBe inferredTypes' expectedTypes)

-- | Parses the given expression and applies 'annotateExprTypes'.
annotateTestExprTypes :: String -> Converter HS.Expr
annotateTestExprTypes input = do
  expr <- parseTestExpr input
  annotateExprTypes expr

-- | Parses the given expression, applies 'annotateExprTypes' nodes and
--   sets the expectation that the given expression is obtained.
shouldAnnotateExprTypes :: String -> String -> Converter Expectation
shouldAnnotateExprTypes input expectedOutput = do
  output  <- annotateTestExprTypes input
  output' <- resolveTypes output
  return (output' `prettyShouldBe` expectedOutput)

-- | Parses the given function declarations and applies
--   'annotateFuncDeclTypes'.
annotateTestFuncDeclTypes :: [String] -> Converter [HS.FuncDecl]
annotateTestFuncDeclTypes input = do
  ([], typeSigs, funcDecls) <- parseTestDecls input
  mapM_ defineTypeSigDecl typeSigs
  annotateFuncDeclTypes funcDecls

-- | Parses the given expression, applies 'annotateFuncDeclTypes' nodes and
--   sets the expectation that the given function declarations are obtained.
shouldAnnotateFuncDeclTypes :: [String] -> [String] -> Converter Expectation
shouldAnnotateFuncDeclTypes input expectedOutput = do
  output  <- annotateTestFuncDeclTypes input
  output' <- mapM resolveTypes output
  return (zipWithM_ prettyShouldBe output' expectedOutput)
