-- | This module contains tests for "FreeC.IR.Reference".

module FreeC.IR.ReferenceTests where

import           Test.Hspec

import           FreeC.IR.Reference
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Test.Parser

-- | Test group for "FreeC.IR.Reference" tests.
testReference :: Spec
testReference = describe "FreeC.IR.Reference" $ do
  testTypeVars

-- | Test group for 'freeTypeVars' tests.
testTypeVars :: Spec
testTypeVars = context "freeTypeVars" $ do
  it "should preserve the order of type arguments" $ do
    typeExpr <- expectParseTestType "C b ((c -> f) -> (e -> d)) a"
    freeTypeVars typeExpr
      `shouldBe` [ IR.UnQual (IR.Ident "b")
                 , IR.UnQual (IR.Ident "c")
                 , IR.UnQual (IR.Ident "f")
                 , IR.UnQual (IR.Ident "e")
                 , IR.UnQual (IR.Ident "d")
                 , IR.UnQual (IR.Ident "a")
                 ]
