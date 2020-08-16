-- | This module contains tests for "FreeC.Pass.CompletePatternPass".
module FreeC.Pass.CompletePatternPassTests where

import           Test.Hspec

import           FreeC.Monad.Class.Testable
import           FreeC.Pass.CompletePatternPass
import           FreeC.Test.Environment
import           FreeC.Test.Parser

-- | Test group for 'completePatternPass' tests.
testCompletePatternPass :: SpecWith ()
testCompletePatternPass = describe "FreeC.Pass.CompletePatternPass" $ do
  context "Top-level case expressions" $ do
    it "fails when a constructor is missing" $ do
      input <- expectParseTestFuncDecl "f x = case x :: Foobar of {Foo -> Foo}"
      shouldFail $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestVar "x"
        checkPatternFuncDecl input
    it "fails when a constructor occurs more than once" $ do
      input <- expectParseTestFuncDecl
        "f x = case x :: Foobar of {Foo -> Foo ; Bar -> Bar ; Foo -> Foo}"
      shouldFail $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestVar "x"
        checkPatternFuncDecl input
    it "succeeds when all constructors occur exactly once" $ do
      input <- expectParseTestFuncDecl
        "f x = case x :: Foobar of {Foo -> Foo ; Bar -> Bar}"
      shouldSucceed $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestVar "x"
        checkPatternFuncDecl input
    it "succeeds when all constructors are given the right number of arguments"
      $ do
        input <- expectParseTestFuncDecl
          "f x = case x :: Foobar of {Foo y -> Foo ; Bar y -> Bar}"
        shouldSucceed $ do
          _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
          _ <- defineTestCon "Foo" 1 "Foobar -> Foobar"
          _ <- defineTestCon "Bar" 0 "Foobar"
          _ <- defineTestVar "x"
          checkPatternFuncDecl input
    it "fails when a constructor of the wrong type occurs" $ do
      input <- expectParseTestFuncDecl
        "f x = case x :: Foobar of {Foo -> Foo ; Bar -> Bar ; Evil -> Bar}"
      shouldFail $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestTypeCon "Evil" 0 [ "Evil" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestCon "Evil" 0 "Evil"
        _ <- defineTestVar "x"
        checkPatternFuncDecl input
  context "Nested and deeper case expressions" $ do
    it "fails for a faulty case expression inside an if statement" $ do
      input <- expectParseTestFuncDecl
        "f x = if b then case x :: Foobar of {Foo -> Foo} else Bar"
      shouldFail $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestVar "x"
        _ <- defineTestVar "b"
        checkPatternFuncDecl input
    it "fails for a faulty nested case expression" $ do
      input <- expectParseTestFuncDecl
        $ "f x = case x :: Foobar of {Foo -> case x :: Foobar of "
        ++ "{Foo -> Foo} ; Bar -> Bar}"
      shouldFail $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestVar "x"
        checkPatternFuncDecl input
    it ("fails for a faulty case expression used as another case expression's"
        ++ "scrutinee") $ do
      input <- expectParseTestFuncDecl
        $ "f x = case ((case x :: Foobar of {Foo -> x} ) :: Foobar) "
        ++ "of {Foo -> Foo ; Bar -> Bar}"
      shouldFail $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestVar "x"
        checkPatternFuncDecl input
    it "succeeds for a valid nested case expression" $ do
      input <- expectParseTestFuncDecl
        $ "f x = case x :: Foobar of {Foo -> case x :: Foobar of "
        ++ "{Foo -> Foo ; Bar -> Bar} ; Bar -> Bar}"
      shouldSucceed $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestVar "x"
        checkPatternFuncDecl input
    it "fails for a faulty case expression inside a lambda expression" $ do
      input <- expectParseTestFuncDecl
        "f x = \\ y -> case x :: Foobar of {Foo -> Foo}"
      shouldFail $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestVar "x"
        checkPatternFuncDecl input
  context "Illegal scrutinee types" $ do
    it ("fails if the case expression's scrutinee is a function and"
        ++ "the alternative list is not empty") $ do
      input <- expectParseTestFuncDecl
        "g f = case f :: Foobar -> Foobar of {Foo -> Foo ; Bar -> Bar}"
      shouldFail $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestFunc "f" 1 "Foobar -> Foobar"
        _ <- defineTestVar "b"
        checkPatternFuncDecl input
    it ("fails if the case expression's scrutinee is a function"
        ++ "and the alternative list is empty") $ do
      input <- expectParseTestFuncDecl "g f = case f :: Foobar -> Foobar of {}"
      shouldFail $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestVar "b"
        checkPatternFuncDecl input
    it ("succeeds if the case expression's scrutinee is a full"
        ++ "function application") $ do
      input <- expectParseTestFuncDecl
        "g x = case (f x) :: Foobar of {Foo -> Foo ; Bar -> Bar}"
      shouldSucceed $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestFunc "f" 1 "Foobar -> Foobar"
        _ <- defineTestVar "x"
        checkPatternFuncDecl input
    it "fails if the case expression's scrutinee is a lambda expression" $ do
      input <- expectParseTestFuncDecl
        $ "f = case (\\ x -> Foo) :: Foobar -> Foobar of "
        ++ "{Foo -> Foo ; Bar -> Bar}"
      shouldFail $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        checkPatternFuncDecl input
    it "fails if the case expression's scrutinee is polymorphic" $ do
      input <- expectParseTestFuncDecl "f x = case x :: a of {}"
      shouldFail $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo", "Bar" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestCon "Bar" 0 "Foobar"
        _ <- defineTestVar "x"
        _ <- defineTestTypeVar "a"
        checkPatternFuncDecl input
  context "Type synonyms" $ do
    it "succeeds for complete pattern matching on a type synonym" $ do
      input
        <- expectParseTestFuncDecl "f x = case x :: FoobarSyn of { Foo -> Foo }"
      shouldSucceed $ do
        _ <- defineTestTypeCon "Foobar" 0 [ "Foo" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestTypeSyn "FoobarSyn" [] "Foobar"
        checkPatternFuncDecl input
    it "succeeds for complete pattern matching on a nested type synonym" $ do
      input
        <- expectParseTestFuncDecl "f x = case x :: FooSynSyn of { Foo -> Foo }"
      shouldSucceed $ do
        _ <- defineTestTypeCon "Foo" 0 [ "Foo" ]
        _ <- defineTestCon "Foo" 0 "Foobar"
        _ <- defineTestTypeSyn "FooSyn" [] "Foo"
        _ <- defineTestTypeSyn "FooSynSyn" [] "FooSyn"
        checkPatternFuncDecl input
