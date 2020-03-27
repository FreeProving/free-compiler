module Compiler.Backend.Coq.Converter.TypeTests where

import           Test.Hspec

import           Compiler.Util.Test

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'convertType' tests.
testConvertType :: Spec
testConvertType =
  describe "Compiler.Backend.Coq.Converter.Type.convertType" $ do
    it "fails to translate unknown type varaibles"
      $ shouldReportFatal
      $ fromConverter
      $ convertTestType "a"

    it "fails to translate unknown type constructor"
      $ shouldReportFatal
      $ fromConverter
      $ convertTestType "NoSuchType"

    it "translates 'a' correctly" $ shouldSucceed $ fromConverter $ do
      "a" <- defineTestTypeVar "a"
      "a" `shouldTranslateTypeTo` "Free Shape Pos a"

    it "translates 'Bool' correctly" $ shouldSucceed $ fromConverter $ do
      "Bool" `shouldTranslateTypeTo` "Free Shape Pos (Bool Shape Pos)"

    it "translates 'Integer' correctly" $ shouldSucceed $ fromConverter $ do
      "Integer" `shouldTranslateTypeTo` "Free Shape Pos (Integer Shape Pos)"

    it "translates custom types correctly" $ shouldSucceed $ fromConverter $ do
      "Foo" <- defineTestTypeCon "Foo" 0
      "Foo" `shouldTranslateTypeTo` "Free Shape Pos (Foo Shape Pos)"

    it "translates '()' correctly" $ shouldSucceed $ fromConverter $ do
      "()" `shouldTranslateTypeTo` "Free Shape Pos (Unit Shape Pos)"

    it "translates '[a]' correctly" $ shouldSucceed $ fromConverter $ do
      "a" <- defineTestTypeVar "a"
      "[a]" `shouldTranslateTypeTo` "Free Shape Pos (List Shape Pos a)"

    it "translates '(a, b)' correctly" $ shouldSucceed $ fromConverter $ do
      "a" <- defineTestTypeVar "a"
      "b" <- defineTestTypeVar "b"
      "(a, b)" `shouldTranslateTypeTo` "Free Shape Pos (Pair Shape Pos a b)"

    it "translates 'a -> b' correctly" $ shouldSucceed $ fromConverter $ do
      "a" <- defineTestTypeVar "a"
      "b" <- defineTestTypeVar "b"
      shouldTranslateTypeTo
        "a -> b"
        "Free Shape Pos (Free Shape Pos a -> Free Shape Pos b)"
