module Compiler.ConverterTests where

import           Test.Hspec

import           Compiler.Converter.Renamer
import           Compiler.MyConverter

import           Compiler.Util.Test

-- | Test group for all @Compiler.Converter@ tests.
testConverter :: Spec
testConverter = describe "Compiler.Converter" $ do
  testConvertDataDecls
  testConvertType

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
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type"
          ++ " := Bar : Foo Shape Pos"
          ++ " |  Baz : Foo Shape Pos."
          -- TODO argument sentences.
          -- TODO smart constructors.

  it "translates polymorphic types correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateDeclsTo "data Foo a b = Bar a | Baz b"
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type)"
          ++ " (a b : Type) : Type"
          ++ " := Bar : Free Shape Pos a -> Foo Shape Pos a b"
          ++ " |  Baz : Free Shape Pos b -> Foo Shape Pos a b."

  it "renames constructors with same name as their data type"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateDeclsTo "data Foo = Foo"
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type"
          ++ " := Foo0 : Foo Shape Pos."
          -- TODO append underscore instead?

  -- TODO smart constructors
  it "renames type variables with same name as constructors"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateDeclsTo "data Foo a = A a"
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type)"
          ++ " (a : Type) : Type"
          ++ " := A : Free Shape Pos a -> Foo Shape Pos a."

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
    "Foo" <- renameAndDefineTypeCon "Foo"
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
