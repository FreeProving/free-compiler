module FreeC.Frontend.IR.ParserTests where

import           Test.Hspec              hiding ( shouldReturn )

import           FreeC.Frontend.IR.Parser
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Reporter
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Expectation setters                                                       --
-------------------------------------------------------------------------------

-- | Sets the expectation that the 'Parseable' instance can accepts the given
--   input and produces the given output.
shouldParse :: (Eq a, Parseable a, Show a) => String -> a -> Expectation
shouldParse input expectedOutput =
  (parseTestIR input :: Parseable a => Reporter a) `shouldReturn` expectedOutput

-- | Like 'shouldParse' for modules.
--
--   Automatically concatenates the lines of the input module.
shouldParseModule :: [String] -> HS.Module -> Expectation
shouldParseModule = shouldParse . unlines

-- | Sets the expectation that the given parser reports a fatal message.
shouldBeParseError :: (Parseable a, Show a) => Reporter a -> Expectation
shouldBeParseError = shouldFail

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------

-- | Test group for "FreeC.Frontend.IR.Parser" tests.
testIRParser :: Spec
testIRParser = describe "FreeC.Frontend.IR.Parser" $ do
  testNameParser
  testQNameParser
  testTypeParser
  testTypeSchemaParser
  testSynTypeDeclParser
  testDataDeclParser
  testTypeSigParser
  testExprParser
  testFuncDeclParser
  testImportDeclParser
  testModuleParser

-------------------------------------------------------------------------------
-- Names                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of 'HS.Name'.
testNameParser :: Spec
testNameParser = context "names" $ do
  it "accepts variable identifiers" $ do
    "x" `shouldParse` HS.Ident "x"
    "foo" `shouldParse` HS.Ident "foo"
    "bar'" `shouldParse` HS.Ident "bar'"
    "fizzBuzz" `shouldParse` HS.Ident "fizzBuzz"
    "fizz_buzz" `shouldParse` HS.Ident "fizz_buzz"
    "qux2" `shouldParse` HS.Ident "qux2"
    "qux₂" `shouldParse` HS.Ident "qux₂"
  it "accepts constructor identifiers" $ do
    "X" `shouldParse` HS.Ident "X"
    "Foo" `shouldParse` HS.Ident "Foo"
    "Bar'" `shouldParse` HS.Ident "Bar'"
    "FizzBuzz" `shouldParse` HS.Ident "FizzBuzz"
    "Fizz_Buzz" `shouldParse` HS.Ident "Fizz_Buzz"
    "Qux2" `shouldParse` HS.Ident "Qux2"
  it "accepts variable symbols" $ do
    "(>>=)" `shouldParse` HS.Symbol ">>="
    "(,)" `shouldParse` HS.Symbol ","
    "(++)" `shouldParse` HS.Symbol "++"
  it "accepts constructor symbols" $ do
    "()" `shouldParse` HS.Symbol ""
    "(:)" `shouldParse` HS.Symbol ":"
    "(:|)" `shouldParse` HS.Symbol ":|"
    "(:.:)" `shouldParse` HS.Symbol ":.:"
  it "rejects identifiers starting with an apostrophe" $ do
    shouldBeParseError (parseTestName "'bar'")
  it "rejects identifiers starting with a digit" $ do
    shouldBeParseError (parseTestName "2qux")

-- | Test group for 'Parseable' instance of 'HS.QName'.
testQNameParser :: Spec
testQNameParser = context "qualifiable names" $ do
  it "accepts unqualified names" $ do
    "foo" `shouldParse` HS.UnQual (HS.Ident "foo")
    "Foo" `shouldParse` HS.UnQual (HS.Ident "Foo")
    "(++)" `shouldParse` HS.UnQual (HS.Symbol "++")
    "(:+:)" `shouldParse` HS.UnQual (HS.Symbol ":+:")
  it "accepts qualified names" $ do
    "Test.foo" `shouldParse` HS.Qual "Test" (HS.Ident "foo")
    "Test.Foo" `shouldParse` HS.Qual "Test" (HS.Ident "Foo")
    "Test.(++)" `shouldParse` HS.Qual "Test" (HS.Symbol "++")
    "Test.(:+:)" `shouldParse` HS.Qual "Test" (HS.Symbol ":+:")
  it "accepts doubly qualified names" $ do
    "M1.M2.foo" `shouldParse` HS.Qual "M1.M2" (HS.Ident "foo")
    "M1.M2.Foo" `shouldParse` HS.Qual "M1.M2" (HS.Ident "Foo")
    "M1.M2.(++)" `shouldParse` HS.Qual "M1.M2" (HS.Symbol "++")
    "M1.M2.(:+:)" `shouldParse` HS.Qual "M1.M2" (HS.Symbol ":+:")
  it "allows qualified names with spaces" $ do
    "M1.M2. foo1" `shouldParse` HS.Qual "M1.M2" (HS.Ident "foo1")
    "M1.M2 .foo2" `shouldParse` HS.Qual "M1.M2" (HS.Ident "foo2")
    "M1. M2.foo3" `shouldParse` HS.Qual "M1.M2" (HS.Ident "foo3")
    "M1 .M2.foo4" `shouldParse` HS.Qual "M1.M2" (HS.Ident "foo4")

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of 'HS.Type'.
testTypeParser :: Spec
testTypeParser = context "type expressions" $ do
  let a  = HS.TypeVar NoSrcSpan "a"
      b  = HS.TypeVar NoSrcSpan "b"
      c  = HS.TypeVar NoSrcSpan "c"
      a' = HS.TypeCon NoSrcSpan (HS.UnQual (HS.Ident "A"))
      b' = HS.TypeCon NoSrcSpan (HS.UnQual (HS.Ident "B"))
  it "accepts unqualified type variables" $ do
    "a" `shouldParse` a
  it "rejects qualified type variables" $ do
    shouldBeParseError (parseTestType "M.a")
  it "accepts type constructors" $ do
    "A" `shouldParse` a'
  it "accepts function types" $ do
    "a -> b" `shouldParse` HS.FuncType NoSrcSpan a b
  it "parses function types right associative" $ do
    "a -> b -> c"
      `shouldParse` HS.FuncType NoSrcSpan a (HS.FuncType NoSrcSpan b c)
  it "accepts type application" $ do
    "A b" `shouldParse` HS.TypeApp NoSrcSpan a' b
  it "parses type application left associative" $ do
    "A b c" `shouldParse` HS.TypeApp NoSrcSpan (HS.TypeApp NoSrcSpan a' b) c
  it "accepts types with parenthesis" $ do
    "(a -> b) -> c"
      `shouldParse` HS.FuncType NoSrcSpan (HS.FuncType NoSrcSpan a b) c
    "A (B c)" `shouldParse` HS.TypeApp NoSrcSpan a' (HS.TypeApp NoSrcSpan b' c)

-- | Test group for 'Parseable' instance of 'HS.TypeSchema'.
testTypeSchemaParser :: Spec
testTypeSchemaParser = context "type schemas" $ do
  let
    a = HS.TypeVarDecl NoSrcSpan "a"
    b = HS.TypeVarDecl NoSrcSpan "b"
    t = HS.FuncType NoSrcSpan
                    (HS.TypeVar NoSrcSpan "a")
                    (HS.TypeVar NoSrcSpan "b")
  it "accepts type schemas without explicit forall" $ do
    "a -> b" `shouldParse` HS.TypeSchema NoSrcSpan [] t
  it "accepts type schemas with explicit empty forall" $ do
    "forall. a -> b" `shouldParse` HS.TypeSchema NoSrcSpan [] t
  it "accepts type schemas with explicit non-empty forall" $ do
    "forall a. a -> b" `shouldParse` HS.TypeSchema NoSrcSpan [a] t
    "forall a b. a -> b" `shouldParse` HS.TypeSchema NoSrcSpan [a, b] t

-------------------------------------------------------------------------------
-- Type declarations                                                         --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of type synonym declarations.
testSynTypeDeclParser :: Spec
testSynTypeDeclParser = context "type synonym declarations" $ do
  it "accepts type synonyms declarations without type arguments"
    $             "type Foo = Bar"
    `shouldParse` HS.TypeSynDecl
                    NoSrcSpan
                    (HS.DeclIdent NoSrcSpan (HS.UnQual (HS.Ident "Foo")))
                    []
                    (HS.TypeCon NoSrcSpan (HS.UnQual (HS.Ident "Bar")))
  it "accepts type synonyms declarations with type arguments"
    $             "type Foo a = Bar a"
    `shouldParse` HS.TypeSynDecl
                    NoSrcSpan
                    (HS.DeclIdent NoSrcSpan (HS.UnQual (HS.Ident "Foo")))
                    [HS.TypeVarDecl NoSrcSpan "a"]
                    (HS.TypeApp
                      NoSrcSpan
                      (HS.TypeCon NoSrcSpan (HS.UnQual (HS.Ident "Bar")))
                      (HS.TypeVar NoSrcSpan "a")
                    )
  it "accepts type synonyms declarations with qualified name"
    $             "type M.Foo = Bar"
    `shouldParse` HS.TypeSynDecl
                    NoSrcSpan
                    (HS.DeclIdent NoSrcSpan (HS.Qual "M" (HS.Ident "Foo")))
                    []
                    (HS.TypeCon NoSrcSpan (HS.UnQual (HS.Ident "Bar")))

-- | Test group for 'Parseable' instance of data type declarations.
testDataDeclParser :: Spec
testDataDeclParser = context "data type declarations" $ do
  let foo = HS.DeclIdent NoSrcSpan (HS.UnQual (HS.Ident "Foo"))
      bar = HS.DeclIdent NoSrcSpan (HS.UnQual (HS.Ident "Bar"))
      baz = HS.DeclIdent NoSrcSpan (HS.UnQual (HS.Ident "Baz"))
  it "accepts data type declarations without constructors"
    $ shouldParse "data Foo"
    $ HS.DataDecl NoSrcSpan foo [] []
  it "accepts data type declarations with a single constructor"
    $ shouldParse "data Foo = Bar"
    $ HS.DataDecl NoSrcSpan foo [] [HS.ConDecl NoSrcSpan bar []]
  it "accepts data type declarations with a multiple constructors"
    $ shouldParse "data Foo = Bar | Baz"
    . HS.DataDecl NoSrcSpan foo []
    $ [HS.ConDecl NoSrcSpan bar [], HS.ConDecl NoSrcSpan baz []]
  it "accepts data type declarations with type arguments"
    $ shouldParse "data Foo a"
    $ HS.DataDecl NoSrcSpan foo [HS.TypeVarDecl NoSrcSpan "a"] []
  it "accepts data type declarations whose constructors have fields" $ do
    let a  = HS.TypeVarDecl NoSrcSpan "a"
        b  = HS.TypeVarDecl NoSrcSpan "b"
        a' = HS.TypeVar NoSrcSpan "a"
        b' = HS.TypeVar NoSrcSpan "b"
    shouldParse "data Foo a b = Bar a | Baz a b"
      . HS.DataDecl NoSrcSpan foo [a, b]
      $ [HS.ConDecl NoSrcSpan bar [a'], HS.ConDecl NoSrcSpan baz [a', b']]
  it "accepts data type declarations with qualified name" $ do
    let foo' = HS.DeclIdent NoSrcSpan (HS.Qual "M" (HS.Ident "Foo"))
    shouldParse "data M.Foo" $ HS.DataDecl NoSrcSpan foo' [] []
  it "accepts data type declarations with qualified constructor names" $ do
    let bar' = HS.DeclIdent NoSrcSpan (HS.Qual "M" (HS.Ident "Bar"))
        baz' = HS.DeclIdent NoSrcSpan (HS.Qual "M" (HS.Ident "Baz"))
    shouldParse "data Foo = M.Bar | M.Baz"
      $ HS.DataDecl NoSrcSpan foo []
      $ [HS.ConDecl NoSrcSpan bar' [], HS.ConDecl NoSrcSpan baz' []]

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of 'HS.TypeSig'.
testTypeSigParser :: Spec
testTypeSigParser = context "type signatures" $ do
  let f  = HS.DeclIdent NoSrcSpan (HS.UnQual (HS.Ident "f"))
      f' = HS.DeclIdent NoSrcSpan (HS.Qual "M" (HS.Ident "f"))
      g  = HS.DeclIdent NoSrcSpan (HS.UnQual (HS.Ident "g"))
      a  = HS.TypeVarDecl NoSrcSpan "a"
      b  = HS.TypeVarDecl NoSrcSpan "b"
      a' = HS.TypeVar NoSrcSpan "a"
      b' = HS.TypeVar NoSrcSpan "b"
      t  = HS.TypeSchema NoSrcSpan [] (HS.FuncType NoSrcSpan a' b')
      t' = HS.TypeSchema NoSrcSpan [a, b] (HS.FuncType NoSrcSpan a' b')
  it "accepts type signatures without forall" $ do
    "f :: a -> b" `shouldParse` HS.TypeSig NoSrcSpan [f] t
  it "accepts type signatures with forall" $ do
    "f :: forall a b. a -> b" `shouldParse` HS.TypeSig NoSrcSpan [f] t'
  it "accepts type signatures for multiple functions" $ do
    "f, g :: a -> b" `shouldParse` HS.TypeSig NoSrcSpan [f, g] t
  it "accepts type signatures for qualified names" $ do
    "M.f :: a -> b" `shouldParse` HS.TypeSig NoSrcSpan [f'] t

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of 'HS.Expr'.
testExprParser :: Spec
testExprParser = context "expressions" $ do
  testConExprParser
  testVarExprParser
  testIntLiteralParser
  testAppExprParser
  testLambdaExprParser
  testIfExprParser
  testCaseExprParser
  testErrorTermParser

-- | Test group for 'Parseable' instance of constructor expressions.
testConExprParser :: Spec
testConExprParser = context "constructors" $ do
  it "accepts constructors" $ do
    "Foo" `shouldParse` HS.Con NoSrcSpan (HS.UnQual (HS.Ident "Foo")) Nothing
  it "accepts constructors with symbolic name" $ do
    "()" `shouldParse` HS.Con NoSrcSpan (HS.UnQual (HS.Symbol "")) Nothing
    "([])" `shouldParse` HS.Con NoSrcSpan (HS.UnQual (HS.Symbol "[]")) Nothing
    "(:)" `shouldParse` HS.Con NoSrcSpan (HS.UnQual (HS.Symbol ":")) Nothing
    "(,)" `shouldParse` HS.Con NoSrcSpan (HS.UnQual (HS.Symbol ",")) Nothing
  it "accepts constructors with qualified name" $ do
    "M.Foo"
      `shouldParse` HS.Con NoSrcSpan (HS.Qual "M" (HS.Ident "Foo")) Nothing

-- | Test group for 'Parseable' instance of variable expressions.
testVarExprParser :: Spec
testVarExprParser = context "variables" $ do
  it "accepts variables" $ do
    "x" `shouldParse` HS.Var NoSrcSpan (HS.UnQual (HS.Ident "x")) Nothing
  it "accepts variables with symbolic name" $ do
    "(+)" `shouldParse` HS.Var NoSrcSpan (HS.UnQual (HS.Symbol "+")) Nothing
  it "accepts variables with qualified name" $ do
    "M.f" `shouldParse` HS.Var NoSrcSpan (HS.Qual "M" (HS.Ident "f")) Nothing

-- | Test group for 'Parseable' instance of function application expressions.
testAppExprParser :: Spec
testAppExprParser = context "function applications" $ do
  let a  = HS.TypeSchema NoSrcSpan [] (HS.TypeVar NoSrcSpan "a")
      f  = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "f")) Nothing
      f' = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "f")) (Just a)
      g  = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "g")) Nothing
      x  = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "x")) Nothing
      x' = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "x")) (Just a)
      y  = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "y")) Nothing
      fx = HS.App NoSrcSpan f x Nothing
      gx = HS.App NoSrcSpan g x Nothing
  it "accepts function applications" $ do
    "f x" `shouldParse` fx
  it "parses function applications left associative" $ do
    "f x y" `shouldParse` HS.App NoSrcSpan fx y Nothing
  it "accepts parenthesis in function applications" $ do
    "f (g x)" `shouldParse` HS.App NoSrcSpan f gx Nothing
  it "accepts function applications with type annotation" $ do
    "f x :: a" `shouldParse` HS.App NoSrcSpan f x (Just a)
  it "accepts function applications with type annotation for argument" $ do
    "f (x :: a)" `shouldParse` HS.App NoSrcSpan f x' Nothing
  it "accepts function applications with type annotation for callee" $ do
    "(f :: a) x" `shouldParse` HS.App NoSrcSpan f' x Nothing

-- | Test group for 'Parseable' instance of lambda abstractions.
testLambdaExprParser :: Spec
testLambdaExprParser = context "lambda abstractions" $ do
  let a     = HS.TypeSchema NoSrcSpan [] a'
      a'    = HS.TypeVar NoSrcSpan "a"
      xPat  = HS.VarPat NoSrcSpan "x" Nothing
      xPat' = HS.VarPat NoSrcSpan "x" (Just a')
      yPat  = HS.VarPat NoSrcSpan "y" Nothing
      x     = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "x")) Nothing
      x'    = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "x")) (Just a)
  it "accepts lambda abstractions with a single argument" $ do
    "\\x -> x" `shouldParse` HS.Lambda NoSrcSpan [xPat] x Nothing
  it "accepts lambda abstractions with a multiple arguments" $ do
    "\\x y -> x" `shouldParse` HS.Lambda NoSrcSpan [xPat, yPat] x Nothing
  it "accepts nested lambda abstractions" $ do
    "\\x -> \\y -> x"
      `shouldParse` HS.Lambda NoSrcSpan
                              [xPat]
                              (HS.Lambda NoSrcSpan [yPat] x Nothing)
                              Nothing
  it "accepts lambda abstractions with type annotated arguments" $ do
    "\\(x :: a) -> x" `shouldParse` HS.Lambda NoSrcSpan [xPat'] x Nothing
  it "accepts lambda abstractions with type annotation for right-hand side" $ do
    "\\x -> x :: a" `shouldParse` HS.Lambda NoSrcSpan [xPat] x' Nothing
  it "accepts lambda abstractions with type annotation" $ do
    "(\\x -> x) :: a" `shouldParse` HS.Lambda NoSrcSpan [xPat] x (Just a)
  it "rejects lambda abstractions without arguments" $ do
    shouldBeParseError (parseTestExpr "\\ -> x")

-- | Test group for 'Parseable' instance of @if@ expressions.
testIfExprParser :: Spec
testIfExprParser = context "if expressions" $ do
  let a  = HS.TypeSchema NoSrcSpan [] (HS.TypeVar NoSrcSpan "a")
      x  = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "x")) Nothing
      y  = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "y")) Nothing
      z  = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "z")) Nothing
      x' = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "x")) (Just a)
      y' = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "y")) (Just a)
      z' = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "z")) (Just a)
  it "accepts if expressions" $ do
    "if x then y else z" `shouldParse` HS.If NoSrcSpan x y z Nothing
  it "accepts if expressions with type annotated conditions" $ do
    "if x :: a then y else z" `shouldParse` HS.If NoSrcSpan x' y z Nothing
  it "accepts if expressions with type annotated branches" $ do
    "if x then y :: a else z :: a" `shouldParse` HS.If NoSrcSpan x y' z' Nothing
  it "accepts if expressions with type annotations" $ do
    "(if x then y else z) :: a" `shouldParse` HS.If NoSrcSpan x y z (Just a)

-- | Test group for 'Parseable' instance of @case@ expressions.
testCaseExprParser :: Spec
testCaseExprParser = context "case expressions" $ do
  let a      = HS.TypeSchema NoSrcSpan [] a'
      a'     = HS.TypeVar NoSrcSpan "a"
      s      = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "s")) Nothing
      x      = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "x")) Nothing
      xPat   = HS.VarPat NoSrcSpan "x" Nothing
      xPat'  = HS.VarPat NoSrcSpan "x" (Just a')
      y      = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "y")) Nothing
      yPat   = HS.VarPat NoSrcSpan "y" Nothing
      fooPat = HS.ConPat NoSrcSpan (HS.UnQual (HS.Ident "Foo"))
      barPat = HS.ConPat NoSrcSpan (HS.UnQual (HS.Ident "Bar"))
  it "accepts empty case expressions" $ do
    "case s of {}" `shouldParse` HS.Case NoSrcSpan s [] Nothing
  it "accepts case expressions with a single alternative" $ do
    "case s of { Foo -> x }"
      `shouldParse` HS.Case NoSrcSpan s [HS.Alt NoSrcSpan fooPat [] x] Nothing
  it "accepts case expressions with multiple alternatives" $ do
    "case s of { Foo -> x; Bar -> y }"
      `shouldParse` HS.Case
                      NoSrcSpan
                      s
                      [ HS.Alt NoSrcSpan fooPat [] x
                      , HS.Alt NoSrcSpan barPat [] y
                      ]
                      Nothing
  it "accepts case expressions with trailing semicolon" $ do
    "case s of { Foo -> x; Bar -> y; }"
      `shouldParse` HS.Case
                      NoSrcSpan
                      s
                      [ HS.Alt NoSrcSpan fooPat [] x
                      , HS.Alt NoSrcSpan barPat [] y
                      ]
                      Nothing
  it "accepts case expressions with variable patterns" $ do
    "case s of { Foo x y -> x }"
      `shouldParse` HS.Case NoSrcSpan
                            s
                            [HS.Alt NoSrcSpan fooPat [xPat, yPat] x]
                            Nothing
  it "accepts case expressions with type annotated variable patterns" $ do
    "case s of { Foo (x :: a) -> x }"
      `shouldParse` HS.Case NoSrcSpan
                            s
                            [HS.Alt NoSrcSpan fooPat [xPat'] x]
                            Nothing
  it "accepts case expressions with type annotations" $ do
    "case s of { Foo x -> x } :: a" `shouldParse` HS.Case
      NoSrcSpan
      s
      [HS.Alt NoSrcSpan fooPat [xPat] x]
      (Just a)

-- | Test group for 'Parseable' instance of error terms.
testErrorTermParser :: Spec
testErrorTermParser = context "error terms" $ do
  let a = HS.TypeSchema NoSrcSpan [] (HS.TypeVar NoSrcSpan "a")
  it "accepts 'undefined'" $ do
    "undefined" `shouldParse` HS.Undefined NoSrcSpan Nothing
  it "accepts 'undefined' with type annotation" $ do
    "undefined :: a" `shouldParse` HS.Undefined NoSrcSpan (Just a)
  it "accepts 'error'" $ do
    "error \"...\"" `shouldParse` HS.ErrorExpr NoSrcSpan "..." Nothing
  it "accepts 'error' with type annotation" $ do
    "error \"...\" :: a" `shouldParse` HS.ErrorExpr NoSrcSpan "..." (Just a)
  it "rejects unapplied 'error'" $ do
    shouldBeParseError (parseTestExpr "error")
  it "rejects standalone string literal" $ do
    shouldBeParseError (parseTestExpr "\"...\"")
  it "requires parenthesis around 'error' in application" $ do
    shouldBeParseError (parseTestExpr "f error \"...\"")

-- | Test group for 'Parseable' instance of visible type applications.
testTypeAppExprParser :: Spec
testTypeAppExprParser = context "visible type applications" $ do
  let a = HS.TypeVar NoSrcSpan "a"
      f = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "f")) Nothing
  it "accepts visible type application of functions" $ do
    "f @a" `shouldParse` HS.TypeAppExpr NoSrcSpan f a Nothing
  it "accepts visible type application of constructors" $ do
    "C @a" `shouldParse` HS.TypeAppExpr NoSrcSpan f a Nothing
  it "accepts visible type application of 'undefined'" $ do
    "undefined @a"
      `shouldParse` HS.TypeAppExpr NoSrcSpan
                                   (HS.Undefined NoSrcSpan Nothing)
                                   a
                                   Nothing
  it "accepts visible type application of 'error'" $ do
    "error @a \"...\""
      `shouldParse` HS.TypeAppExpr NoSrcSpan
                                   (HS.ErrorExpr NoSrcSpan "..." Nothing)
                                   a
                                   Nothing
  it "requires parenthesis around visible type application in application" $ do
    shouldBeParseError (parseTestExpr "f g @a")
  it "rejects visible type application of literals" $ do
    shouldBeParseError (parseTestExpr "42 @a")
  it "rejects visible type application of parenthesized expressions" $ do
    shouldBeParseError (parseTestExpr "(f x) @a")

-- | Test group for 'Parseable' instance of integer literal expressions.
testIntLiteralParser :: Spec
testIntLiteralParser = context "integer literals" $ do
  it "accepts the integer literal zero" $ do
    "0" `shouldParse` HS.IntLiteral NoSrcSpan 0 Nothing
  it "accepts zero with sign" $ do
    "+0" `shouldParse` HS.IntLiteral NoSrcSpan 0 Nothing
    "-0" `shouldParse` HS.IntLiteral NoSrcSpan 0 Nothing
  it "accepts decimal integer literals" $ do
    "42" `shouldParse` HS.IntLiteral NoSrcSpan 42 Nothing
  it "accepts decimal integer literals with sign" $ do
    "+42" `shouldParse` HS.IntLiteral NoSrcSpan 42 Nothing
    "-42" `shouldParse` HS.IntLiteral NoSrcSpan (-42) Nothing
  it "accepts decimal integer literals with leading zeros" $ do
    "007" `shouldParse` HS.IntLiteral NoSrcSpan 7 Nothing
  it "decimal integer literals with leading zeros are not octal" $ do
    "009" `shouldParse` HS.IntLiteral NoSrcSpan 9 Nothing
  it "accepts octal integer literals" $ do
    "0o644" `shouldParse` HS.IntLiteral NoSrcSpan 0o644 Nothing
  it "octal integer literal prefix is case insensitive" $ do
    "0O644" `shouldParse` HS.IntLiteral NoSrcSpan 0o644 Nothing
  it "accepts octal integer literals with sign" $ do
    "+0o755" `shouldParse` HS.IntLiteral NoSrcSpan 0o755 Nothing
    "-0o777" `shouldParse` HS.IntLiteral NoSrcSpan (-0o777) Nothing
  it "accepts hexadecimal integer literals" $ do
    "0x2A" `shouldParse` HS.IntLiteral NoSrcSpan 0x2A Nothing
  it "hexadecimal integer literal prefix is case insensitive" $ do
    "0X2A" `shouldParse` HS.IntLiteral NoSrcSpan 0x2A Nothing
  it "hexadecimal integer literal is case insensitive" $ do
    "0x2a" `shouldParse` HS.IntLiteral NoSrcSpan 0x2A Nothing
  it "accepts hexadecimal integer literals with sign" $ do
    "+0xCAFEBABE" `shouldParse` HS.IntLiteral NoSrcSpan 0xCAFEBABE Nothing
    "-0xCAFEBABE" `shouldParse` HS.IntLiteral NoSrcSpan (-0xCAFEBABE) Nothing

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of function declarations.
testFuncDeclParser :: Spec
testFuncDeclParser = context "function declarations" $ do
  let a     = HS.TypeVar NoSrcSpan "a"
      aDecl = HS.TypeVarDecl NoSrcSpan "a"
      f     = HS.DeclIdent NoSrcSpan (HS.UnQual (HS.Ident "f"))
      f'    = HS.DeclIdent NoSrcSpan (HS.Qual "M" (HS.Ident "f"))
      xPat  = HS.VarPat NoSrcSpan "x" Nothing
      xPat' = HS.VarPat NoSrcSpan "x" (Just a)
      yPat  = HS.VarPat NoSrcSpan "y" Nothing
      x     = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "x")) Nothing
  it "accepts function declarations without arguments" $ do
    "f = x" `shouldParse` HS.FuncDecl NoSrcSpan f [] [] x Nothing
  it "accepts function declarations with a single argument" $ do
    "f x = x" `shouldParse` HS.FuncDecl NoSrcSpan f [] [xPat] x Nothing
  it "accepts function declarations with a multiple arguments" $ do
    "f x y = x" `shouldParse` HS.FuncDecl NoSrcSpan f [] [xPat, yPat] x Nothing
  it "accepts function declarations with a type annotated arguments" $ do
    "f (x :: a) = x" `shouldParse` HS.FuncDecl NoSrcSpan f [] [xPat'] x Nothing
  it "accepts function declarations with annotated return type" $ do
    "f x :: a = x" `shouldParse` HS.FuncDecl NoSrcSpan f [] [xPat] x (Just a)
  it "accepts function declarations with type arguments" $ do
    "f @a = x" `shouldParse` HS.FuncDecl NoSrcSpan f [aDecl] [] x Nothing
  it "accepts function declarations with arguments and type arguments" $ do
    "f @a x = x" `shouldParse` HS.FuncDecl NoSrcSpan f [aDecl] [xPat] x Nothing
  it "accepts function declarations with qualified names" $ do
    "M.f = x" `shouldParse` HS.FuncDecl NoSrcSpan f' [] [] x Nothing

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of 'HS.ImportDecl'.
testImportDeclParser :: Spec
testImportDeclParser = context "import declarations" $ do
  it "accepts import declarations" $ do
    "import M" `shouldParse` HS.ImportDecl NoSrcSpan "M"
  it "accepts import declarations for dotted module names" $ do
    "import M1.M2" `shouldParse` HS.ImportDecl NoSrcSpan "M1.M2"

-- |Test group for 'Parseable' instance of 'HS.Module'.
testModuleParser :: Spec
testModuleParser = context "modules" $ do
  let emptyModule = HS.Module { HS.modSrcSpan   = NoSrcSpan
                              , HS.modName      = undefined -- specify in tests
                              , HS.modImports   = []
                              , HS.modTypeDecls = []
                              , HS.modTypeSigs  = []
                              , HS.modPragmas   = []
                              , HS.modFuncDecls = []
                              }
      conFoo = HS.DeclIdent NoSrcSpan (HS.UnQual (HS.Ident "Foo"))
      tyFoo  = HS.TypeCon NoSrcSpan (HS.UnQual (HS.Ident "Foo"))
      funFoo = HS.DeclIdent NoSrcSpan (HS.UnQual (HS.Ident "foo"))
      conBar = HS.DeclIdent NoSrcSpan (HS.UnQual (HS.Ident "Bar"))
      x      = HS.Var NoSrcSpan (HS.UnQual (HS.Ident "x")) Nothing
      xPat   = HS.VarPat NoSrcSpan "x" Nothing
  it "accepts empty modules" $ do
    "module M where" `shouldParse` emptyModule { HS.modName = "M" }
  it "accepts empty modules with dotted names" $ do
    "module M1.M2 where" `shouldParse` emptyModule { HS.modName = "M1.M2" }
  it "accepts modules with imports" $ do
    shouldParseModule
      ["module M1 where", "import M2"]
      emptyModule { HS.modName    = "M1"
                  , HS.modImports = [HS.ImportDecl NoSrcSpan "M2"]
                  }
  it "accepts modules with type synonyms declarations" $ do
    shouldParseModule
      ["module M where", "type Bar = Foo"]
      emptyModule { HS.modName      = "M"
                  , HS.modTypeDecls = [HS.TypeSynDecl NoSrcSpan conBar [] tyFoo]
                  }
  it "accepts modules with data type declarations" $ do
    shouldParseModule
      ["module M where", "data Foo = Bar"]
      emptyModule
        { HS.modName      = "M"
        , HS.modTypeDecls = [ HS.DataDecl NoSrcSpan
                                          conFoo
                                          []
                                          [HS.ConDecl NoSrcSpan conBar []]
                            ]
        }
  it "accepts modules with type signatures" $ do
    shouldParseModule
      ["module M where", "foo :: Foo"]
      emptyModule
        { HS.modName     = "M"
        , HS.modTypeSigs = [ HS.TypeSig NoSrcSpan
                                        [funFoo]
                                        (HS.TypeSchema NoSrcSpan [] tyFoo)
                           ]
        }
  it "accepts modules with function declarations" $ do
    shouldParseModule
      ["module M where", "foo x = x"]
      emptyModule
        { HS.modName      = "M"
        , HS.modFuncDecls = [HS.FuncDecl NoSrcSpan funFoo [] [xPat] x Nothing]
        }
  it "accepts modules with top-level declarations separated by semicolon" $ do
    shouldParseModule
      ["module M1 where", "import M2;", "type Bar = Foo;"]
      emptyModule { HS.modName      = "M1"
                  , HS.modImports   = [HS.ImportDecl NoSrcSpan "M2"]
                  , HS.modTypeDecls = [HS.TypeSynDecl NoSrcSpan conBar [] tyFoo]
                  }
