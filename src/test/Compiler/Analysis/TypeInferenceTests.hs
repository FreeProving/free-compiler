module Compiler.Analysis.TypeInferenceTests where

import           Test.Hspec

import           Control.Monad.Extra            ( zipWithM_ )

import           Compiler.Analysis.TypeInference
import           Compiler.Environment.Resolver
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

-- | Test group for type 'inferFuncDeclTypes' tests.
testInferFuncDeclTypes :: Spec
testInferFuncDeclTypes =
  describe "Compiler.Analysis.TypeInference.inferFuncDeclTypes" $ do
    it "infers the types of simple functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferFuncDeclTypes
            ["null xs = case xs of { [] -> True; x : xs' -> False }"]
            [ "null @t0 (xs :: [t0]) = (case xs of {"
              ++ "    Prelude.([]) -> True;"
              ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) -> False"
              ++ "  }) :: Prelude.Bool"
            ]
    it "infers the types of recursive functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferFuncDeclTypes
            ["length xs = case xs of { [] -> 0; x : xs' -> 1 + length xs' }"]
            [ "length @t0 (xs :: [t0]) = (case xs of {"
              ++ "    Prelude.([]) -> 0;"
              ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) ->"
              ++ "      (+) 1 (length @t0 xs')"
              ++ "  }) :: Prelude.Integer"
            ]
    it "infers vanishing type arguments correctly in non-recursive functions"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestFunc "true" 0 "forall a. Bool"
          shouldInferFuncDeclTypes
            ["zero = if true && true then 0 else 1"]
            [ "zero @t0 @t1 = (if (&&) (true @t0) (true @t1) then 0 else 1)"
                ++ "  :: Prelude.Integer"
            ]
    it "infers vanishing type arguments correctly in recursive functions"
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
            [ "length @t0 @t1 (xs :: [t0]) = (case xs of {"
              ++ "    Prelude.([]) ->"
              ++ "      if eq @[t1] (Prelude.([]) @t1) (Prelude.([]) @t1)"
              ++ "        then 0"
              ++ "        else 1;"
              ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) ->"
              ++ "      (+) 1 (length @t0 @t1 xs')"
              ++ "  }) :: Prelude.Integer"
            ]
    it
        "infers vanishing type arguments correctly in recursive functions that use functions with vanishing type arguments"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestFunc "true" 0 "forall a. Bool"
          shouldInferFuncDeclTypes
            [ "length xs = case xs of {"
              ++ "    []      -> if true then 0 else 1;"
              ++ "    x : xs' -> 1 + length xs'"
              ++ "  }"
            ]
            [ "length @t0 @t1 (xs :: [t0]) = (case xs of {"
              ++ "    Prelude.([]) ->"
              ++ "      if true @t1 then 0 else 1;"
              ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) ->"
              ++ "      (+) 1 (length @t0 @t1 xs')"
              ++ "  }) :: Prelude.Integer"
            ]
    it
        "infers vanishing type arguments correctly in mutually recursive functions"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestFunc "eq" 2 "a -> a -> Bool"
          shouldInferFuncDeclTypes
            [ "length xs = case xs of {"
            ++ "    []      -> if [] `eq` [] then 0 else 1;"
            ++ "    x : xs' -> 1 + length' xs'"
            ++ "  }"
            , "length' xs = case xs of {"
            ++ "    []      -> if [] `eq` [] then 0 else 1;"
            ++ "    x : xs' -> 1 + length xs'"
            ++ "  }"
            ]
            [ "length @t0 @t1 @t2 (xs :: [t0]) = (case xs of {"
            ++ "    Prelude.([]) ->"
            ++ "      if eq @[t1] (Prelude.([]) @t1) (Prelude.([]) @t1)"
            ++ "        then 0"
            ++ "        else 1;"
            ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) ->"
            ++ "      (+) 1 (length' @t0 @t1 @t2 xs')"
            ++ "  }) :: Prelude.Integer"
            , "length' @t0 @t1 @t2 (xs :: [t0]) = (case xs of {"
            ++ "    Prelude.([]) ->"
            ++ "      if eq @[t2] (Prelude.([]) @t2) (Prelude.([]) @t2)"
            ++ "        then 0"
            ++ "        else 1;"
            ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) ->"
            ++ "      (+) 1 (length @t0 @t1 @t2 xs')"
            ++ "  }) :: Prelude.Integer"
            ]
    it
        "infers vanishing type arguments correctly in mutually recursive functions that use functions with vanishing type arguments"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestFunc "true" 0 "forall a. Bool"
          shouldInferFuncDeclTypes
            [ "length xs = case xs of {"
            ++ "    []      -> if true then 0 else 1;"
            ++ "    x : xs' -> 1 + length' xs'"
            ++ "  }"
            , "length' xs = case xs of {"
            ++ "    []      -> if true then 0 else 1;"
            ++ "    x : xs' -> 1 + length xs'"
            ++ "  }"
            ]
            [ "length @t0 @t1 @t2 (xs :: [t0]) = (case xs of {"
            ++ "    Prelude.([]) ->"
            ++ "      if true @t1 then 0 else 1;"
            ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) ->"
            ++ "      (+) 1 (length' @t0 @t1 @t2 xs')"
            ++ "  }) :: Prelude.Integer"
            , "length' @t0 @t1 @t2 (xs :: [t0]) = (case xs of {"
            ++ "    Prelude.([]) ->"
            ++ "      if true @t2 then 0 else 1;"
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
          shouldInferFuncDeclTypes
            [ "size t = case t of {"
              ++ "    Leaf x -> 1;"
              ++ "    Fork l r -> size l + M.size r"
              ++ "  }"
            ]
            [ "size @t0 (t :: Tree t0) = (case t of {"
              ++ "    Leaf (x :: t0) -> 1;"
              ++ "    Fork (l :: Tree t0) (r :: Tree t0)"
              ++ "      -> (+) (size @t0 l) (M.size @t0 r)"
              ++ "  }) :: Prelude.Integer"
            ]
    it "infers the types of partial functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferFuncDeclTypes
            ["head xs = case xs of { [] -> undefined; x : xs' -> x }"]
            [ "head @t0 (xs :: [t0]) = (case xs of {"
              ++ "    Prelude.([]) -> undefined @t0;"
              ++ "    Prelude.(:) (x :: t0) (xs' :: [t0]) -> x"
              ++ "  }) :: t0"
            ]
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
            [ "foldr @a @b (f :: a -> b -> b) (e :: b) (xs :: [a]) ="
              ++ "  (case xs of {"
              ++ "      Prelude.([]) -> e;"
              ++ "      Prelude.(:) (x :: a) (xs' :: [a]) ->"
              ++ "          f x (foldr @a @b f e xs')"
              ++ "    }) :: b"
            ]
    it "abstracted type variable names don't conflict with user defined names"
      $ shouldSucceed
      $ fromConverter
      $ do
          "null"   <- defineTestFunc "null" 1 "[a] -> Bool"
          "append" <- defineTestFunc "append" 2 "[a] -> [a] -> [a]"
          shouldInferFuncDeclTypes
            ["constTrue :: t0 -> Bool", "constTrue x = null ([] `append` [])"]
            [ "constTrue @t0 @t1 (x :: t0) ="
              ++ "  null @t1 (append @t1 (Prelude.([]) @t1) (Prelude.([]) @t1))"
              ++ "  :: Prelude.Bool"
            ]
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
            [ "intHead (xs :: [Prelude.Integer]) = (case xs of {"
              ++ "    Prelude.([]) ->"
              ++ "        error @Prelude.Integer \"intHead: empty list\";"
              ++ "    Prelude.(:) (x :: Prelude.Integer)"
              ++ "                (xs' :: [Prelude.Integer]) -> x"
              ++ "  }) :: Prelude.Integer"
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
          "42" `shouldInferType` ("42", "Prelude.Integer")
    it "infers the type of predefined constants correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "True" `shouldInferType` ("True", "Prelude.Bool")
    it "infers the type of predefined constructors correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType
            "(42, True)"
            ( "Prelude.(,) @Prelude.Integer @Prelude.Bool 42 True"
            , "(Prelude.Integer, Prelude.Bool)"
            )
    it "infers the type of conditions in if-expressions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType
            "\\c -> if c then 0 else 1"
            ( "\\(c :: Prelude.Bool) -> if c then 0 else 1"
            , "Prelude.Bool -> Prelude.Integer"
            )
    it "infers the type of predefined operations correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType
            "(+)"
            ("(+)", "Prelude.Integer -> Prelude.Integer -> Prelude.Integer")
    it "infers the type of partially applied predefined operations correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType "(+) 42"
                          ("(+) 42", "Prelude.Integer -> Prelude.Integer")
    it "infers the type of polymorphic functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "length" <- defineTestFunc "length" 1 "[a] -> Integer"
          shouldInferType
            "\\xs ys -> length xs + length ys"
            ( "\\(xs :: [t0]) (ys :: [t1]) ->"
              ++ "  (+) (length @t0 xs) (length @t1 ys)"
            , "forall t0 t1. [t0] -> [t1] -> Prelude.Integer"
            )
    it "can match hidden and non-hidden types"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType
            "\\x -> if x then [x, True] else [x, False]"
            ( "\\(x :: Prelude.Bool) -> if x"
            ++ "  then Prelude.(:) @Prelude.Bool x"
            ++ "       (Prelude.(:) @Prelude.Bool True"
            ++ "        (Prelude.([]) @Prelude.Bool))"
            ++ "  else Prelude.(:) @Prelude.Bool x"
            ++ "       (Prelude.(:) @Prelude.Bool False"
            ++ "        (Prelude.([]) @Prelude.Bool))"
            , "Prelude.Bool -> [Prelude.Bool]"
            )
    it "infers the type of expressions with type annotation correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType
            "[] :: [Integer]"
            ("Prelude.([]) @Prelude.Integer", "[Prelude.Integer]")
    it "infers the type of the error term 'undefined' correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType "undefined" ("undefined @t0", "forall t0. t0")
    it "infers the type of the error term 'error \"...\"' correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType "error \"...\"" ("error @t0 \"...\"", "forall t0. t0")
    it "infer the type of variables that shadow variables correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType
            "\\x -> (x, \\x -> x)"
            ( "\\(x :: t0) -> Prelude.(,) @t0 @(t1 -> t1) x (\\(x :: t1) -> x)"
            , "forall t0 t1. t0 -> (t0, t1 -> t1)"
            )
    it "instantiates type variables in expression type signatures"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldInferType
            "[undefined :: (a, b), undefined :: (b, a)] :: [(Integer, Bool)]"
            ( "Prelude.(:) @(Prelude.Integer, Prelude.Bool)"
            ++ "  (undefined @(Prelude.Integer, Prelude.Bool))"
            ++ "  (Prelude.(:) @(Prelude.Integer, Prelude.Bool)"
            ++ "  (undefined @(Prelude.Integer, Prelude.Bool))"
            ++ "  (Prelude.([]) @(Prelude.Integer, Prelude.Bool)))"
            , "[(Prelude.Integer, Prelude.Bool)]")
    it "can match types that contain type synonyms"
      $ shouldSucceed
      $ fromConverter
      $ do
          "Foo" <- defineTestTypeSyn "Foo" [] "[Integer]"
          shouldInferType "[] :: Foo" ("Prelude.([]) @Prelude.Integer", "Foo")
    it "expands type synonyms when necessary"
      $ shouldSucceed
      $ fromConverter
      $ do
          "Foo"  <- defineTestTypeSyn "Foo" [] "[Integer]"
          "head" <- defineTestFunc "head" 1 "[a] -> a"
          shouldInferType
            "head ([] :: Foo)"
            ( "head @Prelude.Integer (Prelude.([]) @Prelude.Integer)"
            , "Prelude.Integer"
            )
    it "rejects lists with heterogeneous element types"
      $ shouldReportFatal
      $ fromConverter
      $ do
          inferTestType "[42, True]"
    it "type arguments of functions are applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "head" <- defineTestFunc "head" 1 "[a] -> a"
          shouldInferType
            "head [1]"
            ( "head @Prelude.Integer (Prelude.(:) @Prelude.Integer 1 "
              ++ "(Prelude.([]) @Prelude.Integer))"
            , "Prelude.Integer"
            )
    it "type arguments of constructor patterns are not applied visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> [a]"
          shouldInferType
            "case f 42 of { [] -> (); (x : xs) -> () }"
            ( "case f @Prelude.Integer 42 of {"
            ++ "    Prelude.([]) -> Prelude.();"
            ++ "    Prelude.(:) (x :: Prelude.Integer)"
            ++ "                (xs :: [Prelude.Integer])"
            ++ "      -> Prelude.()"
            ++ "  }"
            , "()"
            )
    it "does not apply functions shadowed by lambda visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> a"
          shouldInferType
            "\\f x -> f x"
            ( "\\(f :: t0 -> t1) (x :: t0) -> f x"
            , "forall t0 t1. (t0 -> t1) -> t0 -> t1"
            )
    it "does not apply functions shadowed by case visibly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> a"
          shouldInferType
            "case (f, 42) of (f, x) -> f x"
            ( "case Prelude.(,) @(Prelude.Integer -> Prelude.Integer) "
            ++ "                @Prelude.Integer (f @Prelude.Integer) 42 of {"
            ++ "    Prelude.(,) (f :: Prelude.Integer -> Prelude.Integer)"
            ++ "                (x :: Prelude.Integer) -> f x"
            ++ "  }"
            , "Prelude.Integer"
            )
    it "generates distinct fresh type variables in different scopes"
      $ shouldSucceed
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 1 "a -> a"
          shouldInferType
            "(\\x -> f x, \\x -> f x)"
            ( "Prelude.(,) @(t0 -> t0) @(t1 -> t1)"
            ++ "           (\\(x :: t0) -> f @t0 x)"
            ++ "           (\\(x :: t1) -> f @t1 x)"
            , "forall t0 t1. (t0 -> t0, t1 -> t1)"
            )

-------------------------------------------------------------------------------
-- Utility functions                                                         --
-------------------------------------------------------------------------------

-- | Parses and infers the type of the given expression.
inferTestType :: String -> Converter (HS.Expr, HS.TypeSchema)
inferTestType input = do
  expr <- parseTestExpr input
  inferExprType expr

-- | Parses and infers the type of the given expression and sets the
--   expectation that the give type is inferred.
shouldInferType :: String -> (String, String) -> Converter Expectation
shouldInferType input (expectedExpr, expectedType) = do
  (annoatedExpr, inferredType) <- inferTestType input
  annoatedExpr'                <- resolveTypes annoatedExpr
  inferredType'                <- resolveTypes inferredType
  return $ do
    annoatedExpr' `prettyShouldBe` expectedExpr
    inferredType' `prettyShouldBe` expectedType

-- | Parses the given declarations, adds the type signatures to the environment
--   and infers the types of the function declarations.
--
--   There must be no type declarations. The function declarations should form
--   a single strongly connected component of the dependency graph.
--
--   Returns the types of the function declarations in order of their
--   declaration.
inferTestFuncDeclTypes :: [String] -> Converter [HS.FuncDecl]
inferTestFuncDeclTypes input = localEnv $ do
  ([], typeSigs, funcDecls) <- parseTestDecls input
  funcDecls'                <- addTypeSigsToFuncDecls typeSigs funcDecls
  inferFuncDeclTypes funcDecls'

-- | Parses the given function declarations, infers its type schema and sets
--   the expectation that the given type schemas are inferred.
shouldInferFuncDeclTypes :: [String] -> [String] -> Converter Expectation
shouldInferFuncDeclTypes input expectedOutput = do
  output  <- inferTestFuncDeclTypes input
  output' <- mapM resolveTypes output
  return (zipWithM_ prettyShouldBe output' expectedOutput)
