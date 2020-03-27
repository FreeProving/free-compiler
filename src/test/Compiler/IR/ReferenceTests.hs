module Compiler.IR.ReferenceTests where

import           Test.Hspec

import           Compiler.IR.Reference
import qualified Compiler.IR.Syntax            as HS

import           Compiler.Util.Test

-- | Test group for dependency extraction tests.
testReference :: Spec
testReference = describe "Compiler.IR.Reference" $ do
  testTypeVars

-- | Test group for 'freeTypeVars' tests.
testTypeVars :: Spec
testTypeVars = context "freeTypeVars" $ do
  it "should preserve the order of type arguments"
    $ shouldSucceed
    $ fromConverter
    $ do
        typeExpr <- parseTestType "C b ((c -> f) -> (e -> d)) a"
        return
          (          freeTypeVars typeExpr
          `shouldBe` [ HS.UnQual (HS.Ident "b")
                     , HS.UnQual (HS.Ident "c")
                     , HS.UnQual (HS.Ident "f")
                     , HS.UnQual (HS.Ident "e")
                     , HS.UnQual (HS.Ident "d")
                     , HS.UnQual (HS.Ident "a")
                     ]
          )
