module FreeC.Frontend.IR.ParserTests where

import           Test.Hspec              hiding ( shouldReturn )

import           FreeC.Frontend.IR.Parser
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
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
shouldParseModule :: [String] -> IR.Module -> Expectation
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

-- | Test group for 'Parseable' instance of 'IR.Name'.
testNameParser :: Spec
testNameParser = context "names" $ do
  it "accepts variable identifiers" $ do
    "x" `shouldParse` IR.Ident "x"
    "foo" `shouldParse` IR.Ident "foo"
    "bar'" `shouldParse` IR.Ident "bar'"
    "fizzBuzz" `shouldParse` IR.Ident "fizzBuzz"
    "fizz_buzz" `shouldParse` IR.Ident "fizz_buzz"
    "qux2" `shouldParse` IR.Ident "qux2"
    "qux₂" `shouldParse` IR.Ident "qux₂"
  it "accepts constructor identifiers" $ do
    "X" `shouldParse` IR.Ident "X"
    "Foo" `shouldParse` IR.Ident "Foo"
    "Bar'" `shouldParse` IR.Ident "Bar'"
    "FizzBuzz" `shouldParse` IR.Ident "FizzBuzz"
    "Fizz_Buzz" `shouldParse` IR.Ident "Fizz_Buzz"
    "Qux2" `shouldParse` IR.Ident "Qux2"
  it "accepts variable symbols" $ do
    "(>>=)" `shouldParse` IR.Symbol ">>="
    "(,)" `shouldParse` IR.Symbol ","
    "(++)" `shouldParse` IR.Symbol "++"
  it "accepts constructor symbols" $ do
    "()" `shouldParse` IR.Symbol ""
    "(:)" `shouldParse` IR.Symbol ":"
    "(:|)" `shouldParse` IR.Symbol ":|"
    "(:.:)" `shouldParse` IR.Symbol ":.:"
  it "rejects identifiers starting with an apostrophe" $ do
    shouldBeParseError (parseTestName "'bar'")
  it "rejects identifiers starting with a digit" $ do
    shouldBeParseError (parseTestName "2qux")

-- | Test group for 'Parseable' instance of 'IR.QName'.
testQNameParser :: Spec
testQNameParser = context "qualifiable names" $ do
  it "accepts unqualified names" $ do
    "foo" `shouldParse` IR.UnQual (IR.Ident "foo")
    "Foo" `shouldParse` IR.UnQual (IR.Ident "Foo")
    "(++)" `shouldParse` IR.UnQual (IR.Symbol "++")
    "(:+:)" `shouldParse` IR.UnQual (IR.Symbol ":+:")
  it "accepts qualified names" $ do
    "Test.foo" `shouldParse` IR.Qual "Test" (IR.Ident "foo")
    "Test.Foo" `shouldParse` IR.Qual "Test" (IR.Ident "Foo")
    "Test.(++)" `shouldParse` IR.Qual "Test" (IR.Symbol "++")
    "Test.(:+:)" `shouldParse` IR.Qual "Test" (IR.Symbol ":+:")
  it "accepts doubly qualified names" $ do
    "M1.M2.foo" `shouldParse` IR.Qual "M1.M2" (IR.Ident "foo")
    "M1.M2.Foo" `shouldParse` IR.Qual "M1.M2" (IR.Ident "Foo")
    "M1.M2.(++)" `shouldParse` IR.Qual "M1.M2" (IR.Symbol "++")
    "M1.M2.(:+:)" `shouldParse` IR.Qual "M1.M2" (IR.Symbol ":+:")
  it "allows qualified names with spaces" $ do
    "M1.M2. foo1" `shouldParse` IR.Qual "M1.M2" (IR.Ident "foo1")
    "M1.M2 .foo2" `shouldParse` IR.Qual "M1.M2" (IR.Ident "foo2")
    "M1. M2.foo3" `shouldParse` IR.Qual "M1.M2" (IR.Ident "foo3")
    "M1 .M2.foo4" `shouldParse` IR.Qual "M1.M2" (IR.Ident "foo4")

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of 'IR.Type'.
testTypeParser :: Spec
testTypeParser = context "type expressions" $ do
  let a  = IR.TypeVar NoSrcSpan "a"
      b  = IR.TypeVar NoSrcSpan "b"
      c  = IR.TypeVar NoSrcSpan "c"
      a' = IR.TypeCon NoSrcSpan (IR.UnQual (IR.Ident "A"))
      b' = IR.TypeCon NoSrcSpan (IR.UnQual (IR.Ident "B"))
  it "accepts unqualified type variables" $ do
    "a" `shouldParse` a
  it "rejects qualified type variables" $ do
    shouldBeParseError (parseTestType "M.a")
  it "accepts type constructors" $ do
    "A" `shouldParse` a'
  it "accepts function types" $ do
    "a -> b" `shouldParse` IR.FuncType NoSrcSpan a b
  it "parses function types right associative" $ do
    "a -> b -> c"
      `shouldParse` IR.FuncType NoSrcSpan a (IR.FuncType NoSrcSpan b c)
  it "accepts type application" $ do
    "A b" `shouldParse` IR.TypeApp NoSrcSpan a' b
  it "parses type application left associative" $ do
    "A b c" `shouldParse` IR.TypeApp NoSrcSpan (IR.TypeApp NoSrcSpan a' b) c
  it "accepts types with parenthesis" $ do
    "(a -> b) -> c"
      `shouldParse` IR.FuncType NoSrcSpan (IR.FuncType NoSrcSpan a b) c
    "A (B c)" `shouldParse` IR.TypeApp NoSrcSpan a' (IR.TypeApp NoSrcSpan b' c)

-- | Test group for 'Parseable' instance of 'IR.TypeSchema'.
testTypeSchemaParser :: Spec
testTypeSchemaParser = context "type schemas" $ do
  let
    a = IR.TypeVarDecl NoSrcSpan "a"
    b = IR.TypeVarDecl NoSrcSpan "b"
    t = IR.FuncType NoSrcSpan
                    (IR.TypeVar NoSrcSpan "a")
                    (IR.TypeVar NoSrcSpan "b")
  it "accepts type schemas without explicit forall" $ do
    "a -> b" `shouldParse` IR.TypeSchema NoSrcSpan [] t
  it "accepts type schemas with explicit empty forall" $ do
    "forall. a -> b" `shouldParse` IR.TypeSchema NoSrcSpan [] t
  it "accepts type schemas with explicit non-empty forall" $ do
    "forall a. a -> b" `shouldParse` IR.TypeSchema NoSrcSpan [a] t
    "forall a b. a -> b" `shouldParse` IR.TypeSchema NoSrcSpan [a, b] t

-------------------------------------------------------------------------------
-- Type declarations                                                         --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of type synonym declarations.
testSynTypeDeclParser :: Spec
testSynTypeDeclParser = context "type synonym declarations" $ do
  it "accepts type synonyms declarations without type arguments"
    $             "type Foo = Bar"
    `shouldParse` IR.TypeSynDecl
                    NoSrcSpan
                    (IR.DeclIdent NoSrcSpan (IR.UnQual (IR.Ident "Foo")))
                    []
                    (IR.TypeCon NoSrcSpan (IR.UnQual (IR.Ident "Bar")))
  it "accepts type synonyms declarations with type arguments"
    $             "type Foo a = Bar a"
    `shouldParse` IR.TypeSynDecl
                    NoSrcSpan
                    (IR.DeclIdent NoSrcSpan (IR.UnQual (IR.Ident "Foo")))
                    [IR.TypeVarDecl NoSrcSpan "a"]
                    (IR.TypeApp
                      NoSrcSpan
                      (IR.TypeCon NoSrcSpan (IR.UnQual (IR.Ident "Bar")))
                      (IR.TypeVar NoSrcSpan "a")
                    )
  it "accepts type synonyms declarations with qualified name"
    $             "type M.Foo = Bar"
    `shouldParse` IR.TypeSynDecl
                    NoSrcSpan
                    (IR.DeclIdent NoSrcSpan (IR.Qual "M" (IR.Ident "Foo")))
                    []
                    (IR.TypeCon NoSrcSpan (IR.UnQual (IR.Ident "Bar")))

-- | Test group for 'Parseable' instance of data type declarations.
testDataDeclParser :: Spec
testDataDeclParser = context "data type declarations" $ do
  let foo = IR.DeclIdent NoSrcSpan (IR.UnQual (IR.Ident "Foo"))
      bar = IR.DeclIdent NoSrcSpan (IR.UnQual (IR.Ident "Bar"))
      baz = IR.DeclIdent NoSrcSpan (IR.UnQual (IR.Ident "Baz"))
  it "accepts data type declarations without constructors"
    $ shouldParse "data Foo"
    $ IR.DataDecl NoSrcSpan foo [] []
  it "accepts data type declarations with a single constructor"
    $ shouldParse "data Foo = Bar"
    $ IR.DataDecl NoSrcSpan foo [] [IR.ConDecl NoSrcSpan bar []]
  it "accepts data type declarations with a multiple constructors"
    $ shouldParse "data Foo = Bar | Baz"
    . IR.DataDecl NoSrcSpan foo []
    $ [IR.ConDecl NoSrcSpan bar [], IR.ConDecl NoSrcSpan baz []]
  it "accepts data type declarations with type arguments"
    $ shouldParse "data Foo a"
    $ IR.DataDecl NoSrcSpan foo [IR.TypeVarDecl NoSrcSpan "a"] []
  it "accepts data type declarations whose constructors have fields" $ do
    let a  = IR.TypeVarDecl NoSrcSpan "a"
        b  = IR.TypeVarDecl NoSrcSpan "b"
        a' = IR.TypeVar NoSrcSpan "a"
        b' = IR.TypeVar NoSrcSpan "b"
    shouldParse "data Foo a b = Bar a | Baz a b"
      . IR.DataDecl NoSrcSpan foo [a, b]
      $ [IR.ConDecl NoSrcSpan bar [a'], IR.ConDecl NoSrcSpan baz [a', b']]
  it "accepts data type declarations with qualified name" $ do
    let foo' = IR.DeclIdent NoSrcSpan (IR.Qual "M" (IR.Ident "Foo"))
    shouldParse "data M.Foo" $ IR.DataDecl NoSrcSpan foo' [] []
  it "accepts data type declarations with qualified constructor names" $ do
    let bar' = IR.DeclIdent NoSrcSpan (IR.Qual "M" (IR.Ident "Bar"))
        baz' = IR.DeclIdent NoSrcSpan (IR.Qual "M" (IR.Ident "Baz"))
    shouldParse "data Foo = M.Bar | M.Baz"
      $ IR.DataDecl NoSrcSpan foo []
      $ [IR.ConDecl NoSrcSpan bar' [], IR.ConDecl NoSrcSpan baz' []]

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of 'IR.TypeSig'.
testTypeSigParser :: Spec
testTypeSigParser = context "type signatures" $ do
  let f  = IR.DeclIdent NoSrcSpan (IR.UnQual (IR.Ident "f"))
      f' = IR.DeclIdent NoSrcSpan (IR.Qual "M" (IR.Ident "f"))
      g  = IR.DeclIdent NoSrcSpan (IR.UnQual (IR.Ident "g"))
      a  = IR.TypeVarDecl NoSrcSpan "a"
      b  = IR.TypeVarDecl NoSrcSpan "b"
      a' = IR.TypeVar NoSrcSpan "a"
      b' = IR.TypeVar NoSrcSpan "b"
      t  = IR.TypeSchema NoSrcSpan [] (IR.FuncType NoSrcSpan a' b')
      t' = IR.TypeSchema NoSrcSpan [a, b] (IR.FuncType NoSrcSpan a' b')
  it "accepts type signatures without forall" $ do
    "f :: a -> b" `shouldParse` IR.TypeSig NoSrcSpan [f] t
  it "accepts type signatures with forall" $ do
    "f :: forall a b. a -> b" `shouldParse` IR.TypeSig NoSrcSpan [f] t'
  it "accepts type signatures for multiple functions" $ do
    "f, g :: a -> b" `shouldParse` IR.TypeSig NoSrcSpan [f, g] t
  it "accepts type signatures for qualified names" $ do
    "M.f :: a -> b" `shouldParse` IR.TypeSig NoSrcSpan [f'] t

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of 'IR.Expr'.
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
    "Foo" `shouldParse` IR.Con NoSrcSpan (IR.UnQual (IR.Ident "Foo")) Nothing
  it "accepts constructors with symbolic name" $ do
    "()" `shouldParse` IR.Con NoSrcSpan (IR.UnQual (IR.Symbol "")) Nothing
    "([])" `shouldParse` IR.Con NoSrcSpan (IR.UnQual (IR.Symbol "[]")) Nothing
    "(:)" `shouldParse` IR.Con NoSrcSpan (IR.UnQual (IR.Symbol ":")) Nothing
    "(,)" `shouldParse` IR.Con NoSrcSpan (IR.UnQual (IR.Symbol ",")) Nothing
  it "accepts constructors with qualified name" $ do
    "M.Foo"
      `shouldParse` IR.Con NoSrcSpan (IR.Qual "M" (IR.Ident "Foo")) Nothing

-- | Test group for 'Parseable' instance of variable expressions.
testVarExprParser :: Spec
testVarExprParser = context "variables" $ do
  it "accepts variables" $ do
    "x" `shouldParse` IR.Var NoSrcSpan (IR.UnQual (IR.Ident "x")) Nothing
  it "accepts variables with symbolic name" $ do
    "(+)" `shouldParse` IR.Var NoSrcSpan (IR.UnQual (IR.Symbol "+")) Nothing
  it "accepts variables with qualified name" $ do
    "M.f" `shouldParse` IR.Var NoSrcSpan (IR.Qual "M" (IR.Ident "f")) Nothing

-- | Test group for 'Parseable' instance of function application expressions.
testAppExprParser :: Spec
testAppExprParser = context "function applications" $ do
  let a  = IR.TypeSchema NoSrcSpan [] (IR.TypeVar NoSrcSpan "a")
      f  = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "f")) Nothing
      f' = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "f")) (Just a)
      g  = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "g")) Nothing
      x  = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "x")) Nothing
      x' = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "x")) (Just a)
      y  = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "y")) Nothing
      fx = IR.App NoSrcSpan f x Nothing
      gx = IR.App NoSrcSpan g x Nothing
  it "accepts function applications" $ do
    "f x" `shouldParse` fx
  it "parses function applications left associative" $ do
    "f x y" `shouldParse` IR.App NoSrcSpan fx y Nothing
  it "accepts parenthesis in function applications" $ do
    "f (g x)" `shouldParse` IR.App NoSrcSpan f gx Nothing
  it "accepts function applications with type annotation" $ do
    "f x :: a" `shouldParse` IR.App NoSrcSpan f x (Just a)
  it "accepts function applications with type annotation for argument" $ do
    "f (x :: a)" `shouldParse` IR.App NoSrcSpan f x' Nothing
  it "accepts function applications with type annotation for callee" $ do
    "(f :: a) x" `shouldParse` IR.App NoSrcSpan f' x Nothing

-- | Test group for 'Parseable' instance of lambda abstractions.
testLambdaExprParser :: Spec
testLambdaExprParser = context "lambda abstractions" $ do
  let a     = IR.TypeSchema NoSrcSpan [] a'
      a'    = IR.TypeVar NoSrcSpan "a"
      xPat  = IR.VarPat NoSrcSpan "x" Nothing False
      xPat' = IR.VarPat NoSrcSpan "x" (Just a') False
      yPat  = IR.VarPat NoSrcSpan "y" Nothing False
      x     = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "x")) Nothing
      x'    = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "x")) (Just a)
  it "accepts lambda abstractions with a single argument" $ do
    "\\x -> x" `shouldParse` IR.Lambda NoSrcSpan [xPat] x Nothing
  it "accepts lambda abstractions with a multiple arguments" $ do
    "\\x y -> x" `shouldParse` IR.Lambda NoSrcSpan [xPat, yPat] x Nothing
  it "accepts nested lambda abstractions" $ do
    "\\x -> \\y -> x"
      `shouldParse` IR.Lambda NoSrcSpan
                              [xPat]
                              (IR.Lambda NoSrcSpan [yPat] x Nothing)
                              Nothing
  it "accepts lambda abstractions with type annotated arguments" $ do
    "\\(x :: a) -> x" `shouldParse` IR.Lambda NoSrcSpan [xPat'] x Nothing
  it "accepts lambda abstractions with type annotation for right-hand side" $ do
    "\\x -> x :: a" `shouldParse` IR.Lambda NoSrcSpan [xPat] x' Nothing
  it "accepts lambda abstractions with type annotation" $ do
    "(\\x -> x) :: a" `shouldParse` IR.Lambda NoSrcSpan [xPat] x (Just a)
  it "rejects lambda abstractions without arguments" $ do
    shouldBeParseError (parseTestExpr "\\ -> x")

-- | Test group for 'Parseable' instance of @if@ expressions.
testIfExprParser :: Spec
testIfExprParser = context "if expressions" $ do
  let a  = IR.TypeSchema NoSrcSpan [] (IR.TypeVar NoSrcSpan "a")
      x  = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "x")) Nothing
      y  = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "y")) Nothing
      z  = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "z")) Nothing
      x' = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "x")) (Just a)
      y' = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "y")) (Just a)
      z' = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "z")) (Just a)
  it "accepts if expressions" $ do
    "if x then y else z" `shouldParse` IR.If NoSrcSpan x y z Nothing
  it "accepts if expressions with type annotated conditions" $ do
    "if x :: a then y else z" `shouldParse` IR.If NoSrcSpan x' y z Nothing
  it "accepts if expressions with type annotated branches" $ do
    "if x then y :: a else z :: a" `shouldParse` IR.If NoSrcSpan x y' z' Nothing
  it "accepts if expressions with type annotations" $ do
    "(if x then y else z) :: a" `shouldParse` IR.If NoSrcSpan x y z (Just a)

-- | Test group for 'Parseable' instance of @case@ expressions.
testCaseExprParser :: Spec
testCaseExprParser = context "case expressions" $ do
  let a      = IR.TypeSchema NoSrcSpan [] a'
      a'     = IR.TypeVar NoSrcSpan "a"
      s      = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "s")) Nothing
      x      = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "x")) Nothing
      xPat   = IR.VarPat NoSrcSpan "x" Nothing False
      xPat'  = IR.VarPat NoSrcSpan "x" (Just a') False
      y      = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "y")) Nothing
      yPat   = IR.VarPat NoSrcSpan "y" Nothing False
      fooPat = IR.ConPat NoSrcSpan (IR.UnQual (IR.Ident "Foo"))
      barPat = IR.ConPat NoSrcSpan (IR.UnQual (IR.Ident "Bar"))
  it "accepts empty case expressions" $ do
    "case s of {}" `shouldParse` IR.Case NoSrcSpan s [] Nothing
  it "accepts case expressions with a single alternative" $ do
    "case s of { Foo -> x }"
      `shouldParse` IR.Case NoSrcSpan s [IR.Alt NoSrcSpan fooPat [] x False] Nothing
  it "accepts case expressions with multiple alternatives" $ do
    "case s of { Foo -> x; Bar -> y }"
      `shouldParse` IR.Case
                      NoSrcSpan
                      s
                      [ IR.Alt NoSrcSpan fooPat [] x False
                      , IR.Alt NoSrcSpan barPat [] y False
                      ]
                      Nothing
  it "accepts case expressions with trailing semicolon" $ do
    "case s of { Foo -> x; Bar -> y; }"
      `shouldParse` IR.Case
                      NoSrcSpan
                      s
                      [ IR.Alt NoSrcSpan fooPat [] x False
                      , IR.Alt NoSrcSpan barPat [] y False
                      ]
                      Nothing
  it "accepts case expressions with variable patterns" $ do
    "case s of { Foo x y -> x }"
      `shouldParse` IR.Case NoSrcSpan
                            s
                            [IR.Alt NoSrcSpan fooPat [xPat, yPat] x False]
                            Nothing
  it "accepts case expressions with type annotated variable patterns" $ do
    "case s of { Foo (x :: a) -> x }"
      `shouldParse` IR.Case NoSrcSpan
                            s
                            [IR.Alt NoSrcSpan fooPat [xPat'] x False]
                            Nothing
  it "accepts case expressions with type annotations" $ do
    "case s of { Foo x -> x } :: a" `shouldParse` IR.Case
      NoSrcSpan
      s
      [IR.Alt NoSrcSpan fooPat [xPat] x False]
      (Just a)

-- | Test group for 'Parseable' instance of error terms.
testErrorTermParser :: Spec
testErrorTermParser = context "error terms" $ do
  let a = IR.TypeSchema NoSrcSpan [] (IR.TypeVar NoSrcSpan "a")
  it "accepts 'undefined'" $ do
    "undefined" `shouldParse` IR.Undefined NoSrcSpan Nothing
  it "accepts 'undefined' with type annotation" $ do
    "undefined :: a" `shouldParse` IR.Undefined NoSrcSpan (Just a)
  it "accepts 'error'" $ do
    "error \"...\"" `shouldParse` IR.ErrorExpr NoSrcSpan "..." Nothing
  it "accepts 'error' with type annotation" $ do
    "error \"...\" :: a" `shouldParse` IR.ErrorExpr NoSrcSpan "..." (Just a)
  it "rejects unapplied 'error'" $ do
    shouldBeParseError (parseTestExpr "error")
  it "rejects standalone string literal" $ do
    shouldBeParseError (parseTestExpr "\"...\"")
  it "requires parenthesis around 'error' in application" $ do
    shouldBeParseError (parseTestExpr "f error \"...\"")

-- | Test group for 'Parseable' instance of visible type applications.
testTypeAppExprParser :: Spec
testTypeAppExprParser = context "visible type applications" $ do
  let a = IR.TypeVar NoSrcSpan "a"
      f = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "f")) Nothing
  it "accepts visible type application of functions" $ do
    "f @a" `shouldParse` IR.TypeAppExpr NoSrcSpan f a Nothing
  it "accepts visible type application of constructors" $ do
    "C @a" `shouldParse` IR.TypeAppExpr NoSrcSpan f a Nothing
  it "accepts visible type application of 'undefined'" $ do
    "undefined @a"
      `shouldParse` IR.TypeAppExpr NoSrcSpan
                                   (IR.Undefined NoSrcSpan Nothing)
                                   a
                                   Nothing
  it "accepts visible type application of 'error'" $ do
    "error @a \"...\""
      `shouldParse` IR.TypeAppExpr NoSrcSpan
                                   (IR.ErrorExpr NoSrcSpan "..." Nothing)
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
    "0" `shouldParse` IR.IntLiteral NoSrcSpan 0 Nothing
  it "accepts zero with sign" $ do
    "+0" `shouldParse` IR.IntLiteral NoSrcSpan 0 Nothing
    "-0" `shouldParse` IR.IntLiteral NoSrcSpan 0 Nothing
  it "accepts decimal integer literals" $ do
    "42" `shouldParse` IR.IntLiteral NoSrcSpan 42 Nothing
  it "accepts decimal integer literals with sign" $ do
    "+42" `shouldParse` IR.IntLiteral NoSrcSpan 42 Nothing
    "-42" `shouldParse` IR.IntLiteral NoSrcSpan (-42) Nothing
  it "accepts decimal integer literals with leading zeros" $ do
    "007" `shouldParse` IR.IntLiteral NoSrcSpan 7 Nothing
  it "decimal integer literals with leading zeros are not octal" $ do
    "009" `shouldParse` IR.IntLiteral NoSrcSpan 9 Nothing
  it "accepts octal integer literals" $ do
    "0o644" `shouldParse` IR.IntLiteral NoSrcSpan 0o644 Nothing
  it "octal integer literal prefix is case insensitive" $ do
    "0O644" `shouldParse` IR.IntLiteral NoSrcSpan 0o644 Nothing
  it "accepts octal integer literals with sign" $ do
    "+0o755" `shouldParse` IR.IntLiteral NoSrcSpan 0o755 Nothing
    "-0o777" `shouldParse` IR.IntLiteral NoSrcSpan (-0o777) Nothing
  it "accepts hexadecimal integer literals" $ do
    "0x2A" `shouldParse` IR.IntLiteral NoSrcSpan 0x2A Nothing
  it "hexadecimal integer literal prefix is case insensitive" $ do
    "0X2A" `shouldParse` IR.IntLiteral NoSrcSpan 0x2A Nothing
  it "hexadecimal integer literal is case insensitive" $ do
    "0x2a" `shouldParse` IR.IntLiteral NoSrcSpan 0x2A Nothing
  it "accepts hexadecimal integer literals with sign" $ do
    "+0xCAFEBABE" `shouldParse` IR.IntLiteral NoSrcSpan 0xCAFEBABE Nothing
    "-0xCAFEBABE" `shouldParse` IR.IntLiteral NoSrcSpan (-0xCAFEBABE) Nothing

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of function declarations.
testFuncDeclParser :: Spec
testFuncDeclParser = context "function declarations" $ do
  let a     = IR.TypeVar NoSrcSpan "a"
      aDecl = IR.TypeVarDecl NoSrcSpan "a"
      f     = IR.DeclIdent NoSrcSpan (IR.UnQual (IR.Ident "f"))
      f'    = IR.DeclIdent NoSrcSpan (IR.Qual "M" (IR.Ident "f"))
      xPat  = IR.VarPat NoSrcSpan "x" Nothing False
      xPat' = IR.VarPat NoSrcSpan "x" (Just a) False
      yPat  = IR.VarPat NoSrcSpan "y" Nothing False
      x     = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "x")) Nothing
  it "accepts function declarations without arguments" $ do
    "f = x" `shouldParse` IR.FuncDecl NoSrcSpan f [] [] Nothing x
  it "accepts function declarations with a single argument" $ do
    "f x = x" `shouldParse` IR.FuncDecl NoSrcSpan f [] [xPat] Nothing x
  it "accepts function declarations with a multiple arguments" $ do
    "f x y = x" `shouldParse` IR.FuncDecl NoSrcSpan f [] [xPat, yPat] Nothing x
  it "accepts function declarations with a type annotated arguments" $ do
    "f (x :: a) = x" `shouldParse` IR.FuncDecl NoSrcSpan f [] [xPat'] Nothing x
  it "accepts function declarations with annotated return type" $ do
    "f x :: a = x" `shouldParse` IR.FuncDecl NoSrcSpan f [] [xPat] (Just a) x
  it "accepts function declarations with type arguments" $ do
    "f @a = x" `shouldParse` IR.FuncDecl NoSrcSpan f [aDecl] [] Nothing x
  it "accepts function declarations with arguments and type arguments" $ do
    "f @a x = x" `shouldParse` IR.FuncDecl NoSrcSpan f [aDecl] [xPat] Nothing x
  it "accepts function declarations with qualified names" $ do
    "M.f = x" `shouldParse` IR.FuncDecl NoSrcSpan f' [] [] Nothing x

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Test group for 'Parseable' instance of 'IR.ImportDecl'.
testImportDeclParser :: Spec
testImportDeclParser = context "import declarations" $ do
  it "accepts import declarations" $ do
    "import M" `shouldParse` IR.ImportDecl NoSrcSpan "M"
  it "accepts import declarations for dotted module names" $ do
    "import M1.M2" `shouldParse` IR.ImportDecl NoSrcSpan "M1.M2"

-- |Test group for 'Parseable' instance of 'IR.Module'.
testModuleParser :: Spec
testModuleParser = context "modules" $ do
  let emptyModule = IR.Module { IR.modSrcSpan   = NoSrcSpan
                              , IR.modName      = undefined -- specify in tests
                              , IR.modImports   = []
                              , IR.modTypeDecls = []
                              , IR.modTypeSigs  = []
                              , IR.modPragmas   = []
                              , IR.modFuncDecls = []
                              }
      conFoo = IR.DeclIdent NoSrcSpan (IR.UnQual (IR.Ident "Foo"))
      tyFoo  = IR.TypeCon NoSrcSpan (IR.UnQual (IR.Ident "Foo"))
      funFoo = IR.DeclIdent NoSrcSpan (IR.UnQual (IR.Ident "foo"))
      conBar = IR.DeclIdent NoSrcSpan (IR.UnQual (IR.Ident "Bar"))
      x      = IR.Var NoSrcSpan (IR.UnQual (IR.Ident "x")) Nothing
      xPat   = IR.VarPat NoSrcSpan "x" Nothing False
  it "accepts empty modules" $ do
    "module M where" `shouldParse` emptyModule { IR.modName = "M" }
  it "accepts empty modules with dotted names" $ do
    "module M1.M2 where" `shouldParse` emptyModule { IR.modName = "M1.M2" }
  it "accepts modules with imports" $ do
    shouldParseModule
      ["module M1 where", "import M2"]
      emptyModule { IR.modName    = "M1"
                  , IR.modImports = [IR.ImportDecl NoSrcSpan "M2"]
                  }
  it "accepts modules with type synonyms declarations" $ do
    shouldParseModule
      ["module M where", "type Bar = Foo"]
      emptyModule { IR.modName      = "M"
                  , IR.modTypeDecls = [IR.TypeSynDecl NoSrcSpan conBar [] tyFoo]
                  }
  it "accepts modules with data type declarations" $ do
    shouldParseModule
      ["module M where", "data Foo = Bar"]
      emptyModule
        { IR.modName      = "M"
        , IR.modTypeDecls = [ IR.DataDecl NoSrcSpan
                                          conFoo
                                          []
                                          [IR.ConDecl NoSrcSpan conBar []]
                            ]
        }
  it "accepts modules with type signatures" $ do
    shouldParseModule
      ["module M where", "foo :: Foo"]
      emptyModule
        { IR.modName     = "M"
        , IR.modTypeSigs = [ IR.TypeSig NoSrcSpan
                                        [funFoo]
                                        (IR.TypeSchema NoSrcSpan [] tyFoo)
                           ]
        }
  it "accepts modules with function declarations" $ do
    shouldParseModule
      ["module M where", "foo x = x"]
      emptyModule
        { IR.modName      = "M"
        , IR.modFuncDecls = [IR.FuncDecl NoSrcSpan funFoo [] [xPat] Nothing x]
        }
  it "accepts modules with top-level declarations separated by semicolon" $ do
    shouldParseModule
      ["module M1 where", "import M2;", "type Bar = Foo;"]
      emptyModule { IR.modName      = "M1"
                  , IR.modImports   = [IR.ImportDecl NoSrcSpan "M2"]
                  , IR.modTypeDecls = [IR.TypeSynDecl NoSrcSpan conBar [] tyFoo]
                  }
