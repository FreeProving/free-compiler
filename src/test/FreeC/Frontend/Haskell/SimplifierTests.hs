-- | This module contains tests for "FreeC.Frontend.Haskell.Simplifier".
module FreeC.Frontend.Haskell.SimplifierTests ( testSimplifier ) where

import           Control.Monad                     ( (>=>) )
import           Test.Hspec

import           FreeC.Frontend.Haskell.Parser
import           FreeC.Frontend.Haskell.Simplifier
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax                   as IR
import           FreeC.Monad.Class.Testable
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Utility functions                                                         --
-------------------------------------------------------------------------------
-- | Parses a Haskell expression and converts it to IR.
parseAndSimplifyExpr :: String -> Simplifier IR.Expr
parseAndSimplifyExpr = (parseHaskell . mkSrcFile "<test-input>")
  >=> simplifyExpr

-- | Parses the given Haskell and IR expressions, converts the Haskell
--   expression to IR and sets the expectation that the given IR expression is
--   produced.
shouldSimplifyExpr :: String -> String -> Simplifier Expectation
shouldSimplifyExpr input expectedOutput = do
  output <- parseAndSimplifyExpr input
  expectedOutput' <- parseTestExpr expectedOutput
  return (output `shouldBeSimilarTo` expectedOutput')

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------
-- | Test group for "FreeC.Frontend.Haskell.Simplifier" tests.
testSimplifier :: Spec
testSimplifier = describe "FreeC.Frontend.Haskell.Simplifier" $ do
  testSimplifyExpr

-- | Test group for 'simplifyExpr' tests.
testSimplifyExpr :: Spec
testSimplifyExpr = context "simplifyExpr" $ do
  it
    "simplifies single-variable-pattern case expressions to lambda abstractions"
    $ shouldSucceedWith
    $ do
      "case e of { x -> e' }" `shouldSimplifyExpr` "(\\x -> e') e"
