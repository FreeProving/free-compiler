module FreeC.Pass.FlattenExprPassTests ( testFlattenExprPass ) where

import           Test.Hspec

import           FreeC.Monad.Class.Testable
import           FreeC.Pass.FlattenExprPass
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

testFlattenExprPass :: Spec
testFlattenExprPass = describe "FreeC.Pass.FlattenExprPass" $ do
  testFlattenExpr

testFlattenExpr :: Spec
testFlattenExpr = context "flattenExpr" $ do
  it "leaves variables unchanged" $ shouldSucceedWith $ do
    input <- parseTestExpr "f x y"
    output <- flattenExpr input
    return $ output `shouldBeSimilarTo` input
  it "transforms nested functions" $ shouldSucceedWith $ do
    input <- parseTestExpr "f (g x) y"
    expectedOutput <- parseTestExpr "let {z = g x} in f z y"
    output <- flattenExpr input
    return $ output `shouldBeSimilarTo` expectedOutput
  it "leaves visible type application unchanged" $ shouldSucceedWith $ do
    input <- parseTestExpr "f @a x y"
    output <- flattenExpr input
    return $ output `shouldBeSimilarTo` input
  it "leaves visible type application of nested functions unchanged"
    $ shouldSucceedWith
    $ do
      input <- parseTestExpr "f @a (g @b x) y"
      expectedOutput <- parseTestExpr "let {z = g @b x} in f @a z y"
      output <- flattenExpr input
      return $ output `shouldBeSimilarTo` expectedOutput
  it "builds lets inside of lambda expressions" $ shouldSucceedWith $ do
    input <- parseTestExpr "\\x -> f (g x)"
    expectedOutput <- parseTestExpr "\\x -> let {y = g x} in f y"
    output <- flattenExpr input
    return $ output `shouldBeSimilarTo` expectedOutput
  it "applies lambda expressions on introduced variables"
    $ shouldSucceedWith
    $ do
      input <- parseTestExpr "(\\x -> x) (f y)"
      expectedOutput <- parseTestExpr "let {z = f y} in (\\x -> x) z"
      output <- flattenExpr input
      return $ output `shouldBeSimilarTo` expectedOutput
