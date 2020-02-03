module Compiler.Analysis.DependencyExtractionTests where

import           Test.Hspec

import           Compiler.Analysis.DependencyExtraction
import qualified Compiler.Haskell.AST          as HS

import           Compiler.Util.Test

-- | Test group for dependency extraction tests.
testDependencyExtraction :: Spec
testDependencyExtraction =
  describe "Compiler.Analysis.DependencyExtraction" $ do
    testTypeVars

-- | Test group for 'typeVars' tests.
testTypeVars :: Spec
testTypeVars = context "typeVars" $ do
  it "should preserve the order of type arguments"
    $ shouldSucceed
    $ fromConverter
    $ do
        typeExpr <- parseTestType "C b ((c -> f) -> (e -> d)) a"
        return
          (          typeVars typeExpr
          `shouldBe` [ HS.UnQual (HS.Ident "b")
                     , HS.UnQual (HS.Ident "c")
                     , HS.UnQual (HS.Ident "f")
                     , HS.UnQual (HS.Ident "e")
                     , HS.UnQual (HS.Ident "d")
                     , HS.UnQual (HS.Ident "a")
                     ]
          )
