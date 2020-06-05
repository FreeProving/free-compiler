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

testNotValidTypes :: Spec
testNotValidTypes = context "not valid types" $ do
  it "should not accept type variable application" $ do
    input <- expectParseTestType "m a"
    shouldFail $ do
      _ <- defineTestTypeVar "m"
      _ <- defineTestTypeVar "a"
      checkType input
  it "should not accept underapplied applied type constructors" $ do
    input <- expectParseTestType "State Int"
    shouldFail $ do
      _ <- defineTestTypeCon "State" 2
      _ <- defineTestTypeCon "Int" 0
      checkType input
  it "should not accept underapplied applied type synonyms" $ do
    input <- expectParseTestType "State Int"
    shouldFail $ do
      _ <- defineTestTypeSyn "State" ["s", "a"] "s -> (,) s a"
      _ <- defineTestTypeCon "Int" 0
      _ <- defineTestTypeCon "(,)" 2
      checkType input
