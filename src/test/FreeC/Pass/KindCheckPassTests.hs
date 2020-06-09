module FreeC.Pass.KindCheckPassTests where

import           Test.Hspec

import           FreeC.Monad.Class.Testable
import           FreeC.Pass.KindCheckPass
import           FreeC.Test.Environment
import           FreeC.Test.Parser

testKindCheckPass :: Spec
testKindCheckPass = describe "FreeC.Pass.KindCheckPassTests" $ do
  testValidTypes
  testNotValidTypes

testValidTypes :: Spec
testValidTypes = context "valid types" $ do
  it "should accept a single type variable" $ do
    input <- expectParseTestType "a"
    shouldSucceed $ do
      _ <- defineTestTypeVar "a"
      checkType input
  it "should accept constant type constructors" $ do
    input <- expectParseTestType "()"
    shouldSucceed $ do
      _ <- defineTestTypeCon "()" 0
      checkType input
  it "should accept constant type synonyms" $ do
    input <- expectParseTestType "Name"
    shouldSucceed $ do
      _ <- defineTestTypeSyn "Name" [] "String"
      _ <- defineTestTypeCon "String" 0
      checkType input
  it "should accept fully applied type constructors" $ do
    input <- expectParseTestType "State Int Int"
    shouldSucceed $ do
      _ <- defineTestTypeCon "State" 2
      _ <- defineTestTypeCon "Int" 0
      checkType input
  it "should accept fully applied type synonyms" $ do
    input <- expectParseTestType "State Int Int"
    shouldSucceed $ do
      _ <- defineTestTypeSyn "State" ["s", "a"] "s -> (,) s a"
      _ <- defineTestTypeCon "Int" 0
      _ <- defineTestTypeCon "(,)" 2
      checkType input
  it "should accept a single type variable in function type signatures" $ do
    input <- expectParseTestModule
      ["module M where", "f :: forall a. a -> a;", "f x = x;"]
    shouldSucceed $ do
      _ <- defineTestTypeVar "a"
      _ <- defineTestVar "x"
      _ <- defineTestFunc "f" 1 "forall a. a -> a"
      kindCheckPass input
  it "should accept a single type variable in function return types" $ do
    input <- expectParseTestModule ["module M where", "f x :: a = x;"]
    shouldSucceed $ do
      _ <- defineTestTypeVar "a"
      _ <- defineTestVar "x"
      _ <- defineTestFunc "f" 1 "forall a. a -> a"
      kindCheckPass input
  it "should accept a single type variable in type annotated function arguments"
    $ do
        input <- expectParseTestModule ["module M where", "f (x :: a) = x;"]
        shouldSucceed $ do
          _ <- defineTestTypeVar "a"
          _ <- defineTestVar "x"
          _ <- defineTestFunc "f" 1 "forall a. a -> a"
          kindCheckPass input
  it "should accept a single type variable in type annotated variables" $ do
    input <- expectParseTestModule ["module M where", "f x = x :: a;"]
    shouldSucceed $ do
      _ <- defineTestTypeVar "a"
      _ <- defineTestVar "x"
      _ <- defineTestFunc "f" 1 "forall a. a -> a"
      kindCheckPass input
  it
      "should accept a single type variable in type annotated case expression variables"
    $ do
        input <- expectParseTestModule
          ["module M where", "f x = case x of {C (y :: b) -> y};"]
        shouldSucceed $ do
          _ <- defineTestTypeVar "a"
          _ <- defineTestTypeVar "b"
          _ <- defineTestVar "x"
          _ <- defineTestVar "y"
          _ <- defineTestCon "C" 0 "forall a. a"
          _ <- defineTestFunc "f" 1 "forall a b. a -> b"
          kindCheckPass input

testNotValidTypes :: Spec
testNotValidTypes = context "not valid types" $ do
  it "should not accept type variable applications" $ do
    input <- expectParseTestType "m a"
    shouldFail $ do
      _ <- defineTestTypeVar "m"
      _ <- defineTestTypeVar "a"
      checkType input
  it "should not accept overapplied function application" $ do
    input <- expectParseTestType "(a -> b) c"
    shouldFail $ do
      _ <- defineTestTypeVar "a"
      _ <- defineTestTypeVar "b"
      _ <- defineTestTypeVar "c"
      checkType input
  it "should not accept underapplied type constructors" $ do
    input <- expectParseTestType "State Int"
    shouldFail $ do
      _ <- defineTestTypeCon "State" 2
      _ <- defineTestTypeCon "Int" 0
      checkType input
  it "should not accept underapplied type synonyms" $ do
    input <- expectParseTestType "State Int"
    shouldFail $ do
      _ <- defineTestTypeSyn "State" ["s", "a"] "s -> (,) s a"
      _ <- defineTestTypeCon "Int" 0
      _ <- defineTestTypeCon "(,)" 2
      checkType input
  it "should not accept overapplied type constructors" $ do
    input <- expectParseTestType "State Int Int Int"
    shouldFail $ do
      _ <- defineTestTypeCon "State" 2
      _ <- defineTestTypeCon "Int" 0
      checkType input
  it "should not accept overapplied type synonyms" $ do
    input <- expectParseTestType "State Int Int Int"
    shouldFail $ do
      _ <- defineTestTypeSyn "State" ["s", "a"] "s -> (,) s a"
      _ <- defineTestTypeCon "Int" 0
      _ <- defineTestTypeCon "(,)" 2
      checkType input
  it "should not accept type variable applications in function type signatures"
    $ do
        input <- expectParseTestModule
          ["module M where", "f :: forall m a. m a -> m a;", "f x = x;"]
        shouldFail $ do
          _ <- defineTestTypeVar "m"
          _ <- defineTestTypeVar "a"
          _ <- defineTestVar "x"
          _ <- defineTestFunc "f" 1 "forall a. m a -> m a"
          kindCheckPass input
  it "should not accept type variable applications in function return types"
    $ do
        input <- expectParseTestModule ["module M where", "f x :: m a = x;"]
        shouldFail $ do
          _ <- defineTestTypeVar "m"
          _ <- defineTestTypeVar "a"
          _ <- defineTestVar "x"
          _ <- defineTestFunc "f" 1 "forall m a. m a -> m a"
          kindCheckPass input
  it
      "should not accept type variable applications in type annotated function arguments"
    $ do
        input <- expectParseTestModule ["module M where", "f (x :: m a) = x;"]
        shouldFail $ do
          _ <- defineTestTypeVar "m"
          _ <- defineTestTypeVar "a"
          _ <- defineTestVar "x"
          _ <- defineTestFunc "f" 1 "forall m a. m a -> m a"
          kindCheckPass input
  it "should not accept type variable applications in type annotated variables"
    $ do
        input <- expectParseTestModule ["module M where", "f x = x :: m a;"]
        shouldFail $ do
          _ <- defineTestTypeVar "m"
          _ <- defineTestTypeVar "a"
          _ <- defineTestVar "x"
          _ <- defineTestFunc "f" 1 "forall m a. m a -> m a"
          kindCheckPass input
  it
      "should not accept type variable applications in type annotated case expression variables"
    $ do
        input <- expectParseTestModule
          ["module M where", "f x = case x of {C (y :: m b) -> y};"]
        shouldFail $ do
          _ <- defineTestTypeVar "m"
          _ <- defineTestTypeVar "a"
          _ <- defineTestTypeVar "b"
          _ <- defineTestVar "x"
          _ <- defineTestVar "y"
          _ <- defineTestCon "C" 0 "forall a. a"
          _ <- defineTestFunc "f" 1 "forall m a b. a -> m b"
          kindCheckPass input
