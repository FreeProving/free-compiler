module FreeC.Pass.SharingAnalysisPassTests ( testSharingAnalysisPass ) where

import           Test.Hspec

import           FreeC.Monad.Class.Testable
import           FreeC.Pass.SharingAnalysisPass
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

testSharingAnalysisPass :: Spec
testSharingAnalysisPass = describe "FreeC.Pass.SharingAnalysisPass" $ do
  testAnalyseSharingExpr
  testAnalyseLocalSharing

testAnalyseSharingExpr :: Spec
testAnalyseSharingExpr = context "analyseSharingExpr" $ do
  it "introduces 'let'-expression for shared variables" $ shouldSucceedWith $ do
    input <- parseTestExpr "f x x"
    varName <- parseTestQName "x"
    expectedOutput <- parseTestExpr "let {y = x} in f y y"
    output <- analyseSharingExpr [varName] input
    return $ output `shouldBeSimilarTo` expectedOutput
  it "ignores non-local variables" $ shouldSucceedWith $ do
    input <- parseTestExpr "f x x"
    output <- analyseSharingExpr [] input
    return $ output `shouldBeSimilarTo` input
  it "variables in different branches are counted separately"
    $ shouldSucceedWith
    $ do
      input <- parseTestExpr "if b then x else x"
      varName <- parseTestQName "x"
      output <- analyseSharingExpr [varName] input
      return $ output `shouldBeSimilarTo` input

testAnalyseLocalSharing :: Spec
testAnalyseLocalSharing = context "analyseLocalSharing" $ do
  it "introduces 'let'-expression for locally shared variables from 'case'-expr"
    $ shouldSucceedWith
    $ do
      input <- parseTestExpr "case e of {Nothing -> 0; Just x  -> f x x}"
      expectedOutput <- parseTestExpr
        "case e of {Nothing -> 0; Just x  -> let {y = x} in f y y}"
      --expectedOutput <- parseTestExpr "case e of {Nothing -> 0; Just x  -> let {y = x} in f y y}"
      output <- analyseLocalSharing input
      --return $ output `shouldBeSimilarTo` expectedOutput
      return $ expectedOutput `shouldBeSimilarTo` output
  it "introduces 'let'-expression for shared variables from 'lambda'-expr"
    $ shouldSucceedWith
    $ do
      input <- parseTestExpr "\\x -> f x x"
      expectedOutput <- parseTestExpr "\\x -> let {y = x} in f y y"
      output <- analyseLocalSharing input
      return $ output `shouldBeSimilarTo` expectedOutput
  it "introduces 'let'-expressions for nested expressions"
    $ shouldSucceedWith
    $ do
      input <- parseTestExpr "\\y -> \\x -> f x x"
      expectedOutput <- parseTestExpr "\\y -> \\x -> let {z = x} in f z z"
      output <- analyseLocalSharing input
      return $ output `shouldBeSimilarTo` expectedOutput
