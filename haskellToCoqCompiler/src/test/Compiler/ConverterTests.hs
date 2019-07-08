module Compiler.ConverterTests where

import           Test.Hspec

import           Compiler.Converter.Renamer

import           Compiler.Util.Test

-- | Test group for all @Compiler.Converter@ tests.
testConverter :: Spec
testConverter = describe "Compiler.Converter" $ do
  testConvertType

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'convertType' tests.
testConvertType :: Spec
testConvertType = describe "convertType" $ do
  it "translates 'a' correctly" $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "a" `shouldTranslateTypeTo` "Free Shape Pos a"

  it "translates 'Bool' correctly" $ fromConverter $ do
    "Bool" `shouldTranslateTypeTo` "Free Shape Pos (Bool Shape Pos)"

  it "translates 'Int' correctly" $ fromConverter $ do
    "Int" `shouldTranslateTypeTo` "Free Shape Pos (Int Shape Pos)"

  it "translates '()' correctly" $ fromConverter $ do
    "()" `shouldTranslateTypeTo` "Free Shape Pos (Unit Shape Pos)"

  it "translates '[a]' correctly" $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "[a]" `shouldTranslateTypeTo` "Free Shape Pos (List Shape Pos a)"

  it "translates '(a, b)' correctly" $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "b" <- renameAndDefineTypeVar "b"
    "(a, b)" `shouldTranslateTypeTo` "Free Shape Pos (Pair Shape Pos a b)"

  it "translates 'a -> b' correctly" $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "b" <- renameAndDefineTypeVar "b"
    shouldTranslateTypeTo
      "a -> b"
      "Free Shape Pos (Free Shape Pos a -> Free Shape Pos b)"
