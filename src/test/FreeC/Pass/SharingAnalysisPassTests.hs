module FreeC.Pass.SharingAnalysisPassTests ( testSharingAnalysisPass ) where

import Test.Hspec

import FreeC.Monad.Class.Testable
import FreeC.Pass.SharingAnalysisPass
import FreeC.Test.Expectations
import FreeC.Test.Parser

testSharingAnalysisPass :: Spec
testSharingAnalysisPass = describe "FreeC.Pass.SharingAnalysisPass" $ do
  testAnalyseSharingExpr
  testAnalyseLocalSharing

testAnalyseSharingExpr :: Spec
testAnalyseSharingExpr = context "analyseSharingExpr" $ do
  it "introduces 'let'-expression for shared variables"
    $ shouldSucceedWith
    $ do
      input   <- parseTestExpr "x + x"
      varName <- parseTestQName "x"
      expectedOutput <- parseTestExpr "let {y = x} in y + y"
      output  <- analyseSharingExpr [varName] input
      return $ output `shouldBeSimilarTo` expectedOutput
  it "ignores non-local variables"
    $ shouldSucceedWith
    $ do
      input   <- parseTestExpr "x + x"
      output  <- analyseSharingExpr [] input
      return $ output `shouldBeSimilarTo` input
  it
  it "variables in different branches are counted separately"
    $ shouldSucceedWith
    $ do
      input   <- parseTestExpr "if b then x else x"
      varName <- parseTestQName "x"
      output  <- analyseSharingExpr [varName] input
      return $ output `shouldBeSimilarTo` input


testAnalyseLocalSharing :: Spec
testAnalyseLocalSharing = context "analyseLocalSharing" $ do
  it "introduces 'let'-expression for locally shared variables"
    $ shouldSucceedWith
    $ do
      input <- parseTestExpr "case e of {Nothing -> 0; Just x  -> x + x}"
      expectedOutput <- parseTestExpr "case e of {Nothing -> 0; Just x  -> let y = x in y + y}"
      output  <- analyseLocalSharing input
