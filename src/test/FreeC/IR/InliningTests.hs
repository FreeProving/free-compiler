-- | This module contains tests for "FreeC.IR.Inlining".
module FreeC.IR.InliningTests where

import           Test.Hspec

import           FreeC.IR.Inlining          ( inlineExpr, inlineFuncDecls )
import           FreeC.Monad.Class.Testable ( shouldSucceedWith )
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Test.Parser          ( parseTestExpr, parseTestFuncDecl )

-- | Test group for 'inlineExpr' and 'inlineFuncDecls'.
testInlining :: Spec
testInlining = describe "FreeC.IR.Inlining" $ do
  context "inlineExpr" $ do
    it "inlines a simple function" $ shouldSucceedWith $ do
      _ <- defineTestTypeCon "Integer" 0 []
      _ <- defineTestFunc "g" 1 "forall a. a -> a"
      fun <- parseTestFuncDecl "f @a (x :: a) :: a = g @a x"
      expr <- parseTestExpr "f @Integer 42"
      res <- inlineExpr [ fun ] expr
      expected <- parseTestExpr "g @Integer 42"
      return (res `shouldBeSimilarTo` expected)
    it "inlines transitive" $ shouldSucceedWith $ do
      _ <- defineTestTypeCon "Integer" 0 []
      _ <- defineTestFunc "h" 1 "forall a. a -> a"
      funG <- parseTestFuncDecl "g @a (x :: a) :: a = h @a x"
      funF <- parseTestFuncDecl "f @a (x :: a) :: a = g @a x "
      expr <- parseTestExpr "f @Integer 42"
      res <- inlineExpr [ funF, funG ] expr
      expected <- parseTestExpr "h @Integer 42"
      return (res `shouldBeSimilarTo` expected)
    it "inlines in a function application" $ shouldSucceedWith $ do
      _ <- defineTestTypeCon "Integer" 0 []
      _ <- defineTestFunc "h" 1 "forall a. a -> a"
      _ <- defineTestFunc "g" 1 "forall a. a -> a"
      fun <- parseTestFuncDecl "f @a (x :: a) :: a = h @a x"
      expr <- parseTestExpr "g @Integer (f @Integer 42)"
      res <- inlineExpr [ fun ] expr
      expected <- parseTestExpr "g @Integer (h @Integer 42)"
      return (res `shouldBeSimilarTo` expected)
    it "inlines in an if expression" $ shouldSucceedWith $ do
      _ <- defineTestTypeCon "Bool" 0 [ "True", "False" ]
      _ <- defineTestTypeCon "Integer" 0 []
      fun <- parseTestFuncDecl "f @a (x :: a) :: a = x"
      expr <- parseTestExpr
        "if (f @Bool True) then f @Integer 42 else f @Integer 24"
      res <- inlineExpr [ fun ] expr
      expected <- parseTestExpr "if True then 42 else 24"
      return (res `shouldBeSimilarTo` expected)
  context "inlineFuncDecls" $ do
    it "inlines a recursive function correctly" $ shouldSucceedWith $ do
      _ <- defineTestTypeCon "Peano" 0 [ "Zero", "Succ" ]
      _ <- defineTestCon "Zero" 0 "Peano"
      _ <- defineTestCon "Succ" 1 "Peano -> Peano"
      add <- parseTestFuncDecl
        ("add (m :: Peano) (n :: Peano) :: Peano = case m of "
         ++ "{ Zero -> n ; Succ m' -> Succ (add' m n) }")
      add'
        <- parseTestFuncDecl "add' (m :: Peano) (n :: Peano) :: Peano = add m n"
      res <- inlineFuncDecls [ add' ] add
      expected <- parseTestFuncDecl
        ("add (m :: Peano) (n :: Peano) :: Peano = case m of "
         ++ "{ Zero -> n ; Succ m' -> Succ (add m n) }")
      return (res `shouldBeSimilarTo` expected)
    it "inlines the zigzag example correctly" $ shouldSucceedWith $ do
      _ <- defineTestTypeCon "Bool" 0 [ "True", "False" ]
      _ <- defineTestCon "True" 0 "Bool"
      _ <- defineTestCon "False" 0 "Bool"
      _ <- defineTestTypeCon "Tree" 0 [ "Leaf", "Branch" ]
      _ <- defineTestCon "Leaf" 1 "Bool -> Tree"
      _ <- defineTestCon "Branch" 2 "Tree -> Tree -> Tree"
      zig <- parseTestFuncDecl ("zig (t :: Tree) :: Bool = case t of "
                                ++ "{ Leaf n -> n ; Branch l r -> zag l}")
      zag <- parseTestFuncDecl ("zag (t :: Tree) :: Bool = case t of "
                                ++ "{ Leaf n -> n ; Branch l r -> zigzag r}")
      zigzag <- parseTestFuncDecl "zigzag (t :: Tree) :: Bool = zig t"
      res <- inlineFuncDecls [ zigzag, zig ] zag
      expected <- parseTestFuncDecl
        ("zag (t :: Tree) :: Bool = case t of "
         ++ "{ Leaf n -> n ; Branch l r -> case r of "
         ++ "{Leaf n -> n ; Branch l r0  -> zag l}}")
      return (res `shouldBeSimilarTo` expected)
