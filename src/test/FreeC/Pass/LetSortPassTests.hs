-- | This module contains tests for "FreeC.Pass.LetSortPass".
module FreeC.Pass.LetSortPassTests ( testLetSortPass ) where

import           Test.Hspec

import qualified FreeC.IR.Syntax            as IR
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Reporter
import           FreeC.Pass.LetSortPass
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-- | Test group for 'letSortPass' tests.
testLetSortPass :: Spec
testLetSortPass = describe "FreeC.Pass.LetSortPass" $ do
  it "sorts `let`-bindings topologically" $ shouldSucceedWith $ do
    input <- parseTestExpr "let { x = y; y = 42 } in x"
    expectedOutput <- parseTestExpr "let { y = 42; x = y } in x"
    output <- sortLetExprs input :: Reporter IR.Expr
    return (output `shouldBeSimilarTo` expectedOutput)
  it "leaves topologically sorted `let`-bindings unchanged"
    $ shouldSucceedWith
    $ do
      input <- parseTestExpr "let { x = 42; y = x } in y"
      output <- sortLetExprs input :: Reporter IR.Expr
      return (output `shouldBeSimilarTo` input)
  it "rejects recursive `let`-bindings" $ do
    input <- expectParseTestExpr "let { x = x } in x"
    shouldFailPretty $ do
      sortLetExprs input :: Reporter IR.Expr
  it "rejects mutually recursive `let`-bindings" $ do
    input <- expectParseTestExpr "let { x = y; y = x } in y"
    shouldFailPretty $ do
      sortLetExprs input :: Reporter IR.Expr
