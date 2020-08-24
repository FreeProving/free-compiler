-- | This module contains tests for "FreeC.IR.TypeSynExpansionTests".
module FreeC.IR.TypeSynExpansionTests where

import           Test.Hspec

import           FreeC.IR.TypeSynExpansion
import           FreeC.Monad.Class.Testable
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-- | Test group for "FreeC.IR.TypeSynExpansion" tests.
testTypeSynExpansion :: Spec
testTypeSynExpansion = describe "FreeC.IR.TypeSynExpansion" $ do
  testExpandTypeSynonym
  testExpandAllTypeSynonyms

-- | Test group for 'testExpandTypeSynonym' tests.
testExpandTypeSynonym :: Spec
testExpandTypeSynonym = context "expandTypeSynonym" $ do
  it "expands only the outermost type synonym" $ shouldSucceedWith $ do
    _ <- defineTestTypeSyn "Foo" ["a"] "Bar a"
    _ <- defineTestTypeCon "Bar" 1 []
    _ <- defineTestTypeCon "Baz" 0 []
    input <- parseTestType "Foo Baz"
    expectedOutput <- parseTestType "Bar Baz"
    output <- expandTypeSynonym input
    return (output `shouldBeSimilarTo` expectedOutput)
  it "does not expand type synonyms recursively" $ shouldSucceedWith $ do
    _ <- defineTestTypeSyn "Foo" ["a"] "Bar a"
    _ <- defineTestTypeSyn "Bar" ["a"] "Baz a"
    _ <- defineTestTypeCon "Qux" 0 []
    input <- parseTestType "Foo Qux"
    expectedOutput <- parseTestType "Bar Qux"
    output <- expandTypeSynonym input
    return (output `shouldBeSimilarTo` expectedOutput)
  it "does not expand nested type synonyms" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 1 []
    _ <- defineTestTypeSyn "Bar" [] "Baz"
    _ <- defineTestTypeCon "Baz" 0 []
    input <- parseTestType "Foo Bar"
    output <- expandTypeSynonym input
    return (output `shouldBeSimilarTo` input)

-- | Test group for 'expandAllTypeSynonyms' tests.
testExpandAllTypeSynonyms :: Spec
testExpandAllTypeSynonyms = context "expandAllTypeSynonyms" $ do
  it "expands outermost type synonyms" $ shouldSucceedWith $ do
    _ <- defineTestTypeSyn "Foo" ["a"] "Bar a"
    _ <- defineTestTypeCon "Bar" 1 []
    _ <- defineTestTypeCon "Baz" 0 []
    input <- parseTestType "Foo Baz"
    expectedOutput <- parseTestType "Bar Baz"
    output <- expandAllTypeSynonyms input
    return (output `shouldBeSimilarTo` expectedOutput)
  it "expands type synonyms recursively" $ shouldSucceedWith $ do
    _ <- defineTestTypeSyn "Foo" ["a"] "Bar a"
    _ <- defineTestTypeSyn "Bar" ["a"] "Baz a"
    _ <- defineTestTypeCon "Qux" 0 []
    input <- parseTestType "Foo Qux"
    expectedOutput <- parseTestType "Baz Qux"
    output <- expandAllTypeSynonyms input
    return (output `shouldBeSimilarTo` expectedOutput)
  it "expands nested type synonyms" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 1 []
    _ <- defineTestTypeSyn "Bar" [] "Baz"
    _ <- defineTestTypeCon "Baz" 0 []
    input <- parseTestType "Foo Bar"
    expectedOutput <- parseTestType "Foo Baz"
    output <- expandAllTypeSynonyms input
    return (output `shouldBeSimilarTo` expectedOutput)
