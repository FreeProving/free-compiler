module FreeC.IR.InliningTests where

import           Test.Hspec


import           FreeC.IR.Inlining              ( inlineExpr )
import           FreeC.Monad.Class.Testable     ( shouldSucceedWith )
import           FreeC.Test.Expectations
import           FreeC.Test.Environment
import           FreeC.Test.Parser              ( parseTestFuncDecl,
                                                  parseTestExpr )


{-

Gegeben:
g :: a -> a

Soll geinlined werden:
f :: a -> a
f x = g x

Ausdruck, in dem geinlined werden soll:
f 42

Erwartete Ausgabe:
g 42

-}

prog :: [String]
prog = ["module A where",
        "f :: forall a . a -> a",
        "f @a (x :: a) :: a = g @a x"]

testInlining :: Spec
testInlining = describe "FreeC.IR.Inlining" $ do
  context "inlineExpr" $ do
    it "inlines a simple function" $
      shouldSucceedWith $  do
        _ <- defineTestTypeCon "Integer" 0
        _ <- defineTestFunc "g" 1 "forall a. a -> a"
        fun <- parseTestFuncDecl "f @a (x :: a) :: a = g @a x"
        expr <- parseTestExpr "f @Integer 42"
        res <- inlineExpr [fun] expr
        expected <- parseTestExpr "g @Integer 42"
        return (res `shouldBeSimilarTo` expected)
