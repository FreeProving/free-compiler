-- | This module contains tests for "FreeC.IR.Subst".
module FreeC.IR.SubstTests where

import           Test.Hspec

import           FreeC.IR.Subst
import qualified FreeC.IR.Syntax as IR
import           FreeC.Test.Parser

-- | Test group for the 'FreeC.IR.Subst.ApplySubst' instance for expressions.
testExprSubst :: Spec
testExprSubst = do
  describe "FreeC.IR.Subst.composeSubst"
    $ do
      it "applies the second substitution first"
        $ do
          y <- expectParseTestExpr "y"
          z <- expectParseTestExpr "z"
          e <- expectParseTestExpr "x y z"
          let s1    = singleSubst (IR.UnQual (IR.Ident "x")) z
              s2    = singleSubst (IR.UnQual (IR.Ident "x")) y
              subst = s1 `composeSubst` s2
              e'    = applySubst subst e
          expected <- expectParseTestExpr "y y z"
          e' `shouldBe` expected
      it "applies the second substitution to the first"
        $ do
          y <- expectParseTestExpr "y"
          z <- expectParseTestExpr "z"
          e <- expectParseTestExpr "x y z"
          let s1    = singleSubst (IR.UnQual (IR.Ident "y")) z
              s2    = singleSubst (IR.UnQual (IR.Ident "x")) y
              subst = s1 `composeSubst` s2
              e'    = applySubst subst e
          expected <- expectParseTestExpr "z z z"
          e' `shouldBe` expected
  describe "FreeC.IR.Subst.applySubst"
    $ do
      it "cannot substitute variables bound by lambda"
        $ do
          val <- expectParseTestExpr "42"
          e <- expectParseTestExpr "(\\x -> x) x"
          let subst = singleSubst (IR.UnQual (IR.Ident "x")) val
              e'    = applySubst subst e
          expected <- expectParseTestExpr "(\\x -> x) 42"
          e' `shouldBe` expected
      it "cannot substitute variables bound by a case alternative"
        $ do
          val <- expectParseTestExpr "(,) 42 True"
          e <- expectParseTestExpr "case x of { (,) x y -> x }"
          let subst = singleSubst (IR.UnQual (IR.Ident "x")) val
              e'    = applySubst subst e
          expected <- expectParseTestExpr "case (,) 42 True of { (,) x y -> x }"
          e' `shouldBe` expected
