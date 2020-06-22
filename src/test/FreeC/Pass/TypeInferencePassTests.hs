-- | This module contains tests for "FreeC.Pass.TypeInferencePass".

module FreeC.Pass.TypeInferencePassTests
  ( testTypeInferencePass
  )
where

import           Test.Hspec

import           FreeC.IR.DependencyGraph
import           FreeC.IR.Strip
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Pass.TypeInferencePass
import           FreeC.Test.Parser
import           FreeC.Test.Expectations
import           FreeC.Test.Environment

-- | Parses the given function declarations runs the 'typeInferencePass'
--   and sets the expectation that the resulting type annotated function
--   declarations are 'FreeC.IR.Similar.similar' to the expected output.
shouldInferType
  :: DependencyComponent String -> [String] -> Converter Expectation
shouldInferType inputStrs expectedOutputStrs = do
  input           <- parseTestComponent inputStrs
  expectedOutputs <- mapM parseTestFuncDecl expectedOutputStrs
  output          <- typeInferencePass input
  let outputs = map stripExprType (unwrapComponent output)
  return (outputs `shouldBeSimilarTo` expectedOutputs)

-- | Test group for 'typeInferencePass' tests.
testTypeInferencePass :: Spec
testTypeInferencePass = describe "FreeC.Analysis.TypeInference" $ do
  context "error terms" $ do
    it "infers the type of the error term 'undefined' correctly"
      $ shouldSucceedWith
      $ do
          shouldInferType (NonRecursive "f = undefined")
                          ["f @a :: a = undefined @a"]
    it "infers the type of the error term 'error \"...\"' correctly"
      $ shouldSucceedWith
      $ do
          shouldInferType (NonRecursive "f = error \"...\"")
                          ["f @a :: a = error @a \"...\""]

  context "constructors and literals" $ do
    it "infers the type of constant constructors correctly"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Foo" 0 ["Bar"]
          _ <- defineTestCon "Bar" 0 "Foo"
          shouldInferType (NonRecursive "f = Bar") ["f :: Foo = Bar"]
    it "infers the type of constructors with arguments correctly"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Prelude.Integer" 0 []
          _ <- defineTestTypeCon "Foo" 0 ["Bar"]
          _ <- defineTestCon "Bar" 2 "forall a. a -> Foo a"
          shouldInferType
            (NonRecursive "f = Bar 42")
            ["f :: Foo Prelude.Integer = Bar @Prelude.Integer 42"]
    it "infers the type of integer literals correctly" $ shouldSucceedWith $ do
      _ <- defineTestTypeCon "Prelude.Integer" 0 []
      shouldInferType (NonRecursive "f = 42") ["f :: Prelude.Integer = 42"]

  context "function applications" $ do
    it "infers the type of predefined operations correctly"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Foo" 0 []
          _ <- defineTestTypeCon "Bar" 0 []
          _ <- defineTestFunc "foo" 1 "Bar -> Bar -> Foo"
          shouldInferType (NonRecursive "f = foo")
                          ["f :: Bar -> Bar -> Foo = foo"]
    it "infers the type of partially applied predefined operations correctly"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Foo" 0 []
          _ <- defineTestTypeCon "Bar" 0 []
          _ <- defineTestFunc "foo" 1 "Bar -> Bar -> Foo"
          shouldInferType (NonRecursive "f x = foo x")
                          ["f (x :: Bar) :: Bar -> Foo = foo x"]
    it "infers the type of polymorphic function applications correctly"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Foo" 0 []
          _ <- defineTestTypeCon "Bar" 1 []
          _ <- defineTestFunc "foo" 1 "forall a. Bar a -> Foo"
          _ <- defineTestFunc "foos" 0 "Foo -> Foo -> Foo"
          shouldInferType
            (NonRecursive "f x y = foos (foo x) (foo y)")
            [ "f @a @b (x :: Bar a) (y :: Bar b) :: Foo"
                ++ "= foos (foo @a x) (foo @b y)"
            ]

  context "lambda abstractions" $ do
    it "infer the type of arguments that shadow variables correctly"
      $ shouldSucceedWith
      $ do
          shouldInferType (NonRecursive "f x = \\x -> x")
                          ["f @a @b (x :: a) :: b -> b = \\(x :: b) -> x"]
    it "does not apply functions shadowed by lambda visibly"
      $ shouldSucceedWith
      $ do
          _ <- defineTestFunc "g" 1 "forall a. a -> a"
          shouldInferType
            (NonRecursive "f x = \\g -> g x")
            [ "f @a @b (x :: a) :: (a -> b) -> b"
                ++ "  = \\(g :: a -> b) -> g x"
            ]

  context "case expressions" $ do
    it "infers the same type for all alternatives of case expressions"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Bit" 0 ["Zero", "One"]
          _ <- defineTestCon "Zero" 0 "Bit"
          _ <- defineTestCon "One" 0 "Bit"
          shouldInferType
            (NonRecursive
              "f x = case x of { Zero -> undefined; One -> undefined }"
            )
            [ "f @a (x :: Bit) :: a = case x of {"
              ++ "    Zero -> undefined @a;"
              ++ "    One -> undefined @a"
              ++ "  }"
            ]
    it "does not apply functions shadowed by variable pattern visibly"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Foo" 0 ["Foo"]
          _ <- defineTestCon "Foo" 0 "forall a b. (a -> b) -> Foo a b"
          _ <- defineTestFunc "g" 1 "forall a. a -> a"
          shouldInferType
            (NonRecursive "f foo x = case foo of { Foo g -> g x }")
            [ "f @a @b (foo :: Foo a b) (x :: a) :: b"
                ++ "= case foo of { Foo (g :: a -> b) -> g x }"
            ]

  context "if expressions" $ do
    it "infers the type of the condition of if expressions"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Prelude.Bool" 0 []
          _ <- defineTestTypeCon "Prelude.Integer" 0 []
          shouldInferType
            (NonRecursive "f c = if c then 0 else 1")
            [ "f (c :: Prelude.Bool) :: Prelude.Integer"
                ++ " = if c then 0 else 1"
            ]
    it "infers the same type for both branches of if expressions"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Prelude.Bool" 0 ["True"]
          _ <- defineTestCon "True" 0 "Prelude.Bool"
          shouldInferType
            (NonRecursive "f x = if x then undefined else undefined")
            [ "f @a (x :: Prelude.Bool) :: a = if x"
              ++ "  then undefined @a"
              ++ "  else undefined @a"
            ]

  context "expression type signatures" $ do
    it "infers the type of expressions with type annotation correctly"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "List" 1 ["Nil"]
          _ <- defineTestTypeCon "Char" 0 []
          _ <- defineTestCon "Nil" 0 "forall a. List a"
          shouldInferType (NonRecursive "f = Nil :: List Char")
                          ["f :: List Char = Nil @Char"]
    it "instantiates type variables in expression type signatures"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Prelude.Bool" 0 []
          _ <- defineTestTypeCon "Either" 2 []
          shouldInferType
            (  NonRecursive
            $  "f b = if b"
            ++ "    then undefined :: forall a b. Either a b"
            ++ "    else undefined :: forall b a. Either b a"
            )
            [ "f @c @d (b :: Prelude.Bool) :: Either c d = if b"
              ++ "    then undefined @(Either c d)"
              ++ "    else undefined @(Either c d)"
            ]

    context "type synonyms" $ do
      it "can match types that contain type synonyms" $ shouldSucceedWith $ do
        _ <- defineTestTypeCon "Foo" 1 ["Foo"]
        _ <- defineTestTypeCon "Bar" 0 []
        _ <- defineTestTypeSyn "Baz" [] "Foo Bar"
        _ <- defineTestCon "Foo" 1 "forall a. Foo a"
        shouldInferType (NonRecursive "f = Foo :: Baz") ["f :: Baz = Foo @Bar"]
      it "expands type synonyms when necessary" $ shouldSucceedWith $ do
        _ <- defineTestTypeCon "Foo" 1 ["Foo"]
        _ <- defineTestTypeCon "Bar" 0 []
        _ <- defineTestTypeSyn "Baz" [] "Foo Bar"
        _ <- defineTestFunc "unfoo" 1 "forall a. Foo a -> a"
        _ <- defineTestCon "Foo" 1 "forall a. Foo a"
        shouldInferType (NonRecursive "f = unfoo (Foo :: Baz)")
                        ["f :: Bar = unfoo @Bar (Foo @Bar)"]

    context "non-recursive functions" $ do
      it "infers the types of simple simple non-recursive correctly"
        $ shouldSucceedWith
        $ do
            _ <- defineTestTypeCon "Bool" 0 ["True", "False"]
            _ <- defineTestCon "True" 0 "Bool"
            _ <- defineTestCon "False" 0 "Bool"
            _ <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
            _ <- defineTestCon "Nil" 0 "forall a. List a"
            _ <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
            shouldInferType
              (NonRecursive
                "null xs = case xs of { Nil -> True; Cons x xs' -> False }"
              )
              [ "null @a (xs :: List a) :: Bool = case xs of {"
                ++ "    Nil -> True;"
                ++ "    Cons (x :: a) (xs' :: List a) -> False"
                ++ "  }"
              ]
      it "infers vanishing type arguments correctly in non-recursive functions"
        $ shouldSucceedWith
        $ do
            _ <- defineTestTypeCon "Prelude.Bool" 0 []
            _ <- defineTestFunc "eq" 0 "forall a. a -> a -> Prelude.Bool"
            _ <- defineTestTypeCon "List" 1 ["Nil"]
            _ <- defineTestCon "Nil" 0 "forall a. List a"
            shouldInferType
              (NonRecursive "true = eq Nil Nil")
              ["true @a :: Prelude.Bool = eq @(List a) (Nil @a) (Nil @a)"]
      it
          (  "infers vanishing type arguments correctly in non-recursive "
          ++ "functions that use functions with vanishing type arguments"
          )
        $ shouldSucceedWith
        $ do
            _ <- defineTestTypeCon "Prelude.Bool" 0 []
            _ <- defineTestFunc "true" 0 "forall a. Prelude.Bool"
            shouldInferType
              (NonRecursive "true' = if true then true else true")
              [ "true' @a @b @c :: Prelude.Bool = if true @a"
                ++ "  then true @b"
                ++ "  else true @c"
              ]

    context "recursive functions" $ do
      it "infers the types of recursive functions correctly"
        $ shouldSucceedWith
        $ do
            _ <- defineTestTypeCon "Prelude.Integer" 0 []
            _ <- defineTestFunc "succ" 1 "Prelude.Integer -> Prelude.Integer"
            _ <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
            _ <- defineTestCon "Nil" 0 "forall a. List a"
            _ <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
            shouldInferType
              (Recursive
                [ "length xs = case xs of {"
                  ++ "    Nil        -> 0;"
                  ++ "    Cons x xs' -> succ (length xs')"
                  ++ "  }"
                ]
              )
              [ "length @a (xs :: List a) :: Prelude.Integer = case xs of {"
                ++ "    Nil -> 0;"
                ++ "    Cons (x :: a) (xs' :: List a) -> succ (length @a xs')"
                ++ "  }"
              ]
      it "infers vanishing type arguments correctly in recursive functions"
        $ shouldSucceedWith
        $ do
            _ <- defineTestTypeCon "Prelude.Integer" 0 []
            _ <- defineTestFunc "succ" 1 "Prelude.Integer -> Prelude.Integer"
            _ <- defineTestFunc "eq" 0 "forall a. a -> a -> Prelude.Bool"
            _ <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
            _ <- defineTestCon "Nil" 0 "forall a. List a"
            _ <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
            shouldInferType
              (Recursive
                [ "length xs = case xs of {"
                  ++ "    Nil        -> if eq Nil Nil then 0 else 1;"
                  ++ "    Cons x xs' -> succ (length xs')"
                  ++ "  }"
                ]
              )
              [ "length @a @b (xs :: List a) :: Prelude.Integer = case xs of {"
                ++ "    Nil -> if eq @(List b) (Nil @b) (Nil @b) then 0 else 1;"
                ++ "    Cons (x :: a) (xs' :: List a) ->"
                ++ "      succ (length @a @b xs')"
                ++ "  }"
              ]
      it
          (  "infers vanishing type arguments correctly in recursive functions "
          ++ "that use functions with vanishing type arguments"
          )
        $ shouldSucceedWith
        $ do
            _ <- defineTestTypeCon "Prelude.Integer" 0 []
            _ <- defineTestFunc "succ" 1 "Prelude.Integer -> Prelude.Integer"
            _ <- defineTestFunc "true" 0 "forall a. Prelude.Bool"
            _ <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
            _ <- defineTestCon "Nil" 0 "forall a. List a"
            _ <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
            shouldInferType
              (Recursive
                [ "length xs = case xs of {"
                  ++ "    Nil        -> if true then 0 else 1;"
                  ++ "    Cons x xs' -> succ (length xs')"
                  ++ "  }"
                ]
              )
              [ "length @a @b (xs :: List a) :: Prelude.Integer = case xs of {"
                ++ "    Nil -> if true @b then 0 else 1;"
                ++ "    Cons (x :: a) (xs' :: List a) ->"
                ++ "      succ (length @a @b xs')"
                ++ "  }"
              ]

    context "mutually recursive functions" $ do
      it "infers the types of mutually recursive functions correctly"
        $ shouldSucceedWith
        $ do
            _ <- defineTestTypeCon "Prelude.Integer" 0 []
            _ <- defineTestFunc "succ" 1 "Prelude.Integer -> Prelude.Integer"
            _ <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
            _ <- defineTestCon "Nil" 0 "forall a. List a"
            _ <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
            shouldInferType
              (Recursive
                [ "length xs = case xs of {"
                ++ "    Nil        -> 0;"
                ++ "    Cons x xs' -> succ (length' xs')"
                ++ "  }"
                , "length' xs = case xs of {"
                ++ "    Nil        -> 0;"
                ++ "    Cons x xs' -> succ (length xs')"
                ++ "  }"
                ]
              )
              [ "length @a (xs :: List a) :: Prelude.Integer = case xs of {"
              ++ "    Nil -> 0;"
              ++ "    Cons (x :: a) (xs' :: List a) -> succ (length' @a xs')"
              ++ "  }"
              , "length' @a (xs :: List a) :: Prelude.Integer = case xs of {"
              ++ "    Nil -> 0;"
              ++ "    Cons (x :: a) (xs' :: List a) -> succ (length @a xs')"
              ++ "  }"
              ]
    it "infers vanishing type arguments correctly in recursive functions"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Prelude.Integer" 0 []
          _ <- defineTestFunc "succ" 1 "Prelude.Integer -> Prelude.Integer"
          _ <- defineTestFunc "eq" 0 "forall a. a -> a -> Prelude.Bool"
          _ <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
          _ <- defineTestCon "Nil" 0 "forall a. List a"
          _ <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
          shouldInferType
            (Recursive
              [ "length xs = case xs of {"
                ++ "    Nil        -> if eq Nil Nil then 0 else 1;"
                ++ "    Cons x xs' -> succ (length xs')"
                ++ "  }"
              ]
            )
            [ "length @a @b (xs :: List a) :: Prelude.Integer = case xs of {"
              ++ "    Nil -> if eq @(List b) (Nil @b) (Nil @b) then 0 else 1;"
              ++ "    Cons (x :: a) (xs' :: List a) ->"
              ++ "      succ (length @a @b xs')"
              ++ "  }"
            ]
    it
        (  "infers vanishing type arguments correctly in recursive functions "
        ++ "that use functions with vanishing type arguments"
        )
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Prelude.Integer" 0 []
          _ <- defineTestFunc "succ" 1 "Prelude.Integer -> Prelude.Integer"
          _ <- defineTestFunc "true" 0 "forall a. Prelude.Bool"
          _ <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
          _ <- defineTestCon "Nil" 0 "forall a. List a"
          _ <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
          shouldInferType
            (Recursive
              [ "length xs = case xs of {"
                ++ "    Nil        -> if true then 0 else 1;"
                ++ "    Cons x xs' -> succ (length xs')"
                ++ "  }"
              ]
            )
            [ "length @a @b (xs :: List a) :: Prelude.Integer = case xs of {"
              ++ "    Nil -> if true @b then 0 else 1;"
              ++ "    Cons (x :: a) (xs' :: List a) ->"
              ++ "      succ (length @a @b xs')"
              ++ "  }"
            ]

  context "mutually recursive functions" $ do
    it "infers the types of mutually recursive functions correctly"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Prelude.Integer" 0 []
          _ <- defineTestFunc "succ" 1 "Prelude.Integer -> Prelude.Integer"
          _ <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
          _ <- defineTestCon "Nil" 0 "forall a. List a"
          _ <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
          shouldInferType
            (Recursive
              [ "length xs = case xs of {"
              ++ "    Nil        -> 0;"
              ++ "    Cons x xs' -> succ (length' xs')"
              ++ "  }"
              , "length' xs = case xs of {"
              ++ "    Nil        -> 0;"
              ++ "    Cons x xs' -> succ (length xs')"
              ++ "  }"
              ]
            )
            [ "length @a (xs :: List a) :: Prelude.Integer = case xs of {"
            ++ "    Nil -> 0;"
            ++ "    Cons (x :: a) (xs' :: List a) -> succ (length' @a xs')"
            ++ "  }"
            , "length' @a (xs :: List a) :: Prelude.Integer = case xs of {"
            ++ "    Nil -> 0;"
            ++ "    Cons (x :: a) (xs' :: List a) -> succ (length @a xs')"
            ++ "  }"
            ]
    it
        (  "infers vanishing type arguments correctly in mutually recursive "
        ++ "functions"
        )
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Prelude.Integer" 0 []
          _ <- defineTestFunc "succ" 1 "Prelude.Integer -> Prelude.Integer"
          _ <- defineTestFunc "eq" 0 "forall a. a -> a -> Prelude.Bool"
          _ <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
          _ <- defineTestCon "Nil" 0 "forall a. List a"
          _ <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
          shouldInferType
            (Recursive
              [ "length xs = case xs of {"
              ++ "    Nil        -> if eq Nil Nil then 0 else 1;"
              ++ "    Cons x xs' -> succ (length' xs')"
              ++ "  }"
              , "length' xs = case xs of {"
              ++ "    Nil        -> if eq Nil Nil then 0 else 1;"
              ++ "    Cons x xs' -> succ (length xs')"
              ++ "  }"
              ]
            )
            [ "length @a @b @c (xs :: List a) :: Prelude.Integer"
            ++ "  = case xs of {"
            ++ "      Nil -> if eq @(List b) (Nil @b) (Nil @b) then 0 else 1;"
            ++ "      Cons (x :: a) (xs' :: List a) ->"
            ++ "        succ (length' @a @b @c xs')"
            ++ "    }"
            , "length' @a @b @c (xs :: List a) :: Prelude.Integer"
            ++ "  = case xs of {"
            ++ "      Nil -> if eq @(List c) (Nil @c) (Nil @c) then 0 else 1;"
            ++ "      Cons (x :: a) (xs' :: List a) ->"
            ++ "        succ (length @a @b @c xs')"
            ++ "    }"
            ]
    it
        (  "infers vanishing type arguments correctly in mutually recursive "
        ++ "functions that use functions with vanishing type arguments"
        )
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Prelude.Integer" 0 []
          _ <- defineTestFunc "succ" 1 "Prelude.Integer -> Prelude.Integer"
          _ <- defineTestFunc "true" 0 "forall a. Prelude.Bool"
          _ <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
          _ <- defineTestCon "Nil" 0 "forall a. List a"
          _ <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
          shouldInferType
            (Recursive
              [ "length xs = case xs of {"
              ++ "    Nil        -> if true then 0 else 1;"
              ++ "    Cons x xs' -> succ (length' xs')"
              ++ "  }"
              , "length' xs = case xs of {"
              ++ "    Nil        -> if true then 0 else 1;"
              ++ "    Cons x xs' -> succ (length xs')"
              ++ "  }"
              ]
            )
            [ "length @a @b @c (xs :: List a) :: Prelude.Integer"
            ++ "  = case xs of {"
            ++ "      Nil -> if true @b then 0 else 1;"
            ++ "      Cons (x :: a) (xs' :: List a) ->"
            ++ "        succ (length' @a @b @c xs')"
            ++ "    }"
            , "length' @a @b @c (xs :: List a) :: Prelude.Integer"
            ++ "  = case xs of {"
            ++ "      Nil -> if true @c then 0 else 1;"
            ++ "      Cons (x :: a) (xs' :: List a) ->"
            ++ "        succ (length @a @b @c xs')"
            ++ "    }"
            ]

  context "functions type signatures" $ do
    it "allows argument type annotation to make type more specific"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Foo" 0 []
          shouldInferType (NonRecursive "fooId (x :: Foo) = x")
                          ["fooId (x :: Foo) :: Foo = x"]
    it "allows return type annotation to make type more specific"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "Foo" 0 []
          shouldInferType (NonRecursive "fooId x :: Foo = x")
                          ["fooId (x :: Foo) :: Foo = x"]

  context "rigid type variables" $ do
    it "cannot match rigid type variable with type constructor" $ do
      funcDecl <- expectParseTestFuncDecl "foo @a (x :: a) :: Foo = x"
      shouldFailPretty $ do
        _ <- defineTestTypeCon "Foo" 0 []
        typeInferencePass (NonRecursive funcDecl)

    it "cannot match type constructor with rigid type variable" $ do
      funcDecl <- expectParseTestFuncDecl "foo @a (x :: a) :: a = Foo"
      shouldFailPretty $ do
        _ <- defineTestTypeCon "Foo" 0 ["Foo"]
        _ <- defineTestCon "Foo" 0 "Foo"
        typeInferencePass (NonRecursive funcDecl)

    it "cannot match two rigid type variables" $ do
      funcDecl <- expectParseTestFuncDecl
        "foo @a @b (x :: a) (y :: b) :: Foo a a = Foo x y"
      shouldFailPretty $ do
        _ <- defineTestTypeCon "Foo" 2 ["Foo"]
        _ <- defineTestCon "Foo" 2 "forall a b. a -> b -> Foo a b"
        typeInferencePass (NonRecursive funcDecl)
