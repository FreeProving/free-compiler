module Compiler.ConverterTests where

import           Test.Hspec

import           Compiler.Converter.Renamer
import           Compiler.Converter

import           Compiler.Util.Test

-- | Test group for all @Compiler.Converter@ tests.
testConverter :: Spec
testConverter = describe "Compiler.Converter" $ do
  testConvertDataDecls
  testConvertType
  testConvertExpr

-------------------------------------------------------------------------------
-- Data type declarations                                                    --
-------------------------------------------------------------------------------

-- | Test group for 'convertDataDecls' tests.
testConvertDataDecls :: Spec
testConvertDataDecls = describe "convertDataDecls" $ do
  it "translates non-polymorphic types correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateDeclsTo "data Foo = Bar | Baz"
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
          ++ " := bar : Foo Shape Pos "
          ++ " |  baz : Foo Shape Pos. "
          ++ "(* Arguments sentences for Foo *) "
          ++ "Arguments bar {Shape} {Pos}. "
          ++ "Arguments baz {Shape} {Pos}. "
          ++ "(* Smart constructors for Foo *) "
          ++ "Definition Bar (Shape : Type) (Pos : Shape -> Type) "
          ++ " : Free Shape Pos (Foo Shape Pos) := pure bar. "
          ++ "Definition Baz (Shape : Type) (Pos : Shape -> Type) "
          ++ " : Free Shape Pos (Foo Shape Pos) := pure baz."

  it "translates polymorphic types correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateDeclsTo "data Foo a b = Bar a | Baz b"
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type) "
          ++ " (a b : Type) : Type "
          ++ " := bar : Free Shape Pos a -> Foo Shape Pos a b "
          ++ " |  baz : Free Shape Pos b -> Foo Shape Pos a b. "
          ++ "(* Arguments sentences for Foo *) "
          ++ "Arguments bar {Shape} {Pos} {a} {b}. "
          ++ "Arguments baz {Shape} {Pos} {a} {b}. "
          ++ "(* Smart constructors for Foo *) "
          ++ "Definition Bar (Shape : Type) (Pos : Shape -> Type) "
          ++ " {a b : Type} (_0 : Free Shape Pos a) "
          ++ " : Free Shape Pos (Foo Shape Pos a b) := pure (bar _0). "
          ++ "Definition Baz (Shape : Type) (Pos : Shape -> Type) "
          ++ " {a b : Type} (_0 : Free Shape Pos b) "
          ++ " : Free Shape Pos (Foo Shape Pos a b) := pure (baz _0)."

  it "renames constructors with same name as their data type"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateDeclsTo "data Foo = Foo"
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
          ++ " := foo : Foo Shape Pos. "
          ++ "(* Arguments sentences for Foo *) "
          ++ "Arguments foo {Shape} {Pos}. "
          ++ "(* Smart constructors for Foo *) "
          ++ "Definition Foo0 (Shape : Type) (Pos : Shape -> Type) "
          ++ " : Free Shape Pos (Foo Shape Pos) := pure foo."

  it "renames type variables with same name as constructors"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateDeclsTo "data Foo a = A a"
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type) "
          ++ " (a0 : Type) : Type "
          ++ " := a : Free Shape Pos a0 -> Foo Shape Pos a0. "
          ++ "(* Arguments sentences for Foo *) "
          ++ "Arguments a {Shape} {Pos} {a0}. "
          ++ "(* Smart constructors for Foo *) "
          ++ "Definition A (Shape : Type) (Pos : Shape -> Type) "
          ++ " {a0 : Type} (_0 : Free Shape Pos a0) "
          ++ " : Free Shape Pos (Foo Shape Pos a0) := pure (a _0)."

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'convertType' tests.
testConvertType :: Spec
testConvertType = describe "convertType" $ do
  it "fails to translate unknown type varaibles"
    $ shouldReportFatal
    $ fromConverter
    $ do
        parseTestType "a" >>= convertType

  it "fails to translate unknown type constructor"
    $ shouldReportFatal
    $ fromConverter
    $ do
        parseTestType "NoSuchType" >>= convertType

  it "translates 'a' correctly" $ shouldSucceed $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "a" `shouldTranslateTypeTo` "Free Shape Pos a"

  it "translates 'Bool' correctly" $ shouldSucceed $ fromConverter $ do
    "Bool" `shouldTranslateTypeTo` "Free Shape Pos (Bool Shape Pos)"

  it "translates 'Int' correctly" $ shouldSucceed $ fromConverter $ do
    "Int" `shouldTranslateTypeTo` "Free Shape Pos (Int Shape Pos)"

  it "translates custom types correctly" $ shouldSucceed $ fromConverter $ do
    "Foo" <- renameAndDefineTypeCon "Foo" 0
    "Foo" `shouldTranslateTypeTo` "Free Shape Pos (Foo Shape Pos)"

  it "translates '()' correctly" $ shouldSucceed $ fromConverter $ do
    "()" `shouldTranslateTypeTo` "Free Shape Pos (Unit Shape Pos)"

  it "translates '[a]' correctly" $ shouldSucceed $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "[a]" `shouldTranslateTypeTo` "Free Shape Pos (List Shape Pos a)"

  it "translates '(a, b)' correctly" $ shouldSucceed $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "b" <- renameAndDefineTypeVar "b"
    "(a, b)" `shouldTranslateTypeTo` "Free Shape Pos (Pair Shape Pos a b)"

  it "translates 'a -> b' correctly" $ shouldSucceed $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "b" <- renameAndDefineTypeVar "b"
    shouldTranslateTypeTo
      "a -> b"
      "Free Shape Pos (Free Shape Pos a -> Free Shape Pos b)"

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Test group for 'convertExpr' tests.
testConvertExpr :: Spec
testConvertExpr = describe "convertExpr" $ do
  testConvertLists
  testConvertTuples

-- | Test group for translation of list expressions.
testConvertLists :: Spec
testConvertLists = context "lists" $ do
  it "translates empty list constructor correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "[]" `shouldTranslateExprTo` "Nil Shape Pos"

  it "translates non-empty list constructor correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "x"  <- renameAndDefineVar "x"
        "xs" <- renameAndDefineVar "xs"
        "x : xs" `shouldTranslateExprTo` "Cons Shape Pos x xs"

  it "translates list literal correctly" $ shouldSucceed $ fromConverter $ do
    "x1" <- renameAndDefineVar "x1"
    "x2" <- renameAndDefineVar "x2"
    "x3" <- renameAndDefineVar "x3"
    shouldTranslateExprTo "[x1, x2, x3]"
      $  "Cons Shape Pos x1 ("
      ++ "Cons Shape Pos x2 ("
      ++ "Cons Shape Pos x3 ("
      ++ "Nil Shape Pos)))"

-- | Test group for translation of tuple expressions.
testConvertTuples :: Spec
testConvertTuples = context "tuples" $ do
  it "translates unit literals correctly" $ shouldSucceed $ fromConverter $ do
    "()" `shouldTranslateExprTo` "Tt Shape Pos"

  it "translates pair literals correctly" $ shouldSucceed $ fromConverter $ do
    "x" <- renameAndDefineVar "x"
    "y" <- renameAndDefineVar "y"
    "(x, y)" `shouldTranslateExprTo` "Pair_ Shape Pos x y"

  it "translates pair constructor correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "x" <- renameAndDefineVar "x"
        "y" <- renameAndDefineVar "y"
        "(,) x y" `shouldTranslateExprTo` "Pair_ Shape Pos x y"
