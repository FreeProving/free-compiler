module FreeC.Pass.InlineLambdaPassTests ( testInlineLambdaPass ) where

import           Test.Hspec

import           FreeC.Pass.InlineLambdaPass
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

testInlineLambdaPass :: Spec
testInlineLambdaPass = describe "FreeC.Pass.InlineLambdaPass" $ do
  it "inlines lambda abstractions into `in`-expressions" $ do
    input <- expectParseTestExpr "let { f = \\x -> g x } in f x"
    expectedOutput <- expectParseTestExpr "(\\x -> g x) x"
    let output = inlineLambdaExpr input
    output `shouldBeSimilarTo` expectedOutput
  it "inlines lambda abstractions into other bindings" $ do
    input <- expectParseTestExpr "let { f = \\x -> g x; y = f x} in y"
    expectedOutput <- expectParseTestExpr "let { y = (\\x -> g x) x } in y"
    let output = inlineLambdaExpr input
    output `shouldBeSimilarTo` expectedOutput
  it "keeps bindings whose right-hand side are not lambda abstractions" $ do
    input <- expectParseTestExpr "let { f = \\x -> g x; x = 42 } in f x"
    expectedOutput <- expectParseTestExpr "let { x = 42 } in (\\x -> g x) x"
    let output = inlineLambdaExpr input
    output `shouldBeSimilarTo` expectedOutput
