-- | This module contains tests for the 'Pretty' instance of IR modules.
module FreeC.IR.Syntax.ModuleTests ( testModuleSyntax ) where

import           Test.Hspec

import           FreeC.Pretty
import           FreeC.Test.Parser

-- | Sets the expectation that after parsing an AST node from the given string
--   and pretty printing the resulting node, the original string is obtained.
shouldPrettyPrintModule :: [ String ] -> Expectation
shouldPrettyPrintModule inputs = do
  node <- expectParseTestModule inputs
  lines (showPretty node) `shouldBe` inputs

-- | Test group for 'Pretty' instances of IR AST nodes.
testModuleSyntax :: Spec
testModuleSyntax = describe "FreeC.IR.Syntax.Module" $ do
  context "instance (Pretty IR.Module)" $ do
    it "separates top-level entries with semi-colons" $ do
      shouldPrettyPrintModule ["module M where", "foo = 42;", "bar = 1337"]
