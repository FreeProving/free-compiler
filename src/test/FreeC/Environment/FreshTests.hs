-- | This module contains tests for "FreeC.Environment.Fresh".
module FreeC.Environment.FreshTests where

import           Test.Hspec

import           FreeC.Environment.Fresh
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Environment

-- | Test group for "FreeC.Environment.Fresh" tests.
testFreshIdentifiers :: Spec
testFreshIdentifiers = describe "FreeC.Environment.Fresh" $ do
  context "freshCoqIdent" $ do
    it "avoids collision with other fresh identifiers" $ shouldSucceedWith $ do
      x0 <- freshCoqIdent "x"
      x1 <- freshCoqIdent "x"
      return ((x0, x1) `shouldBe` ("x_0", "x_1"))
    it "avoids collision with user defined identifiers" $ shouldSucceedWith $ do
      "x_0" <- defineTestVar "x_0"
      x1 <- freshCoqIdent "x" -- 'x@0' is renamed to 'x_1'
      x2 <- freshCoqIdent "x" -- 'x@1' is renamed to 'x_2'
      return ((x1, x2) `shouldBe` ("x_1", "x_2"))
    it "is affected by local environments" $ shouldSucceedWith $ do
      x1 <- localEnv $ do
        "x_0" <- defineTestVar "x_0"
        freshCoqIdent "x" -- 'x@0' is renamed to 'x_1'
      x0 <- localEnv $ freshCoqIdent "x"
      return ((x1, x0) `shouldBe` ("x_1", "x_0"))
