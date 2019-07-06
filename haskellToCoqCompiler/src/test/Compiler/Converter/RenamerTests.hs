module Compiler.Converter.RenamerTests where

import           Test.Hspec
import           Test.QuickCheck

import           Compiler.Converter.Renamer
import           Compiler.Converter.State
import           Compiler.Language.Coq.Keywords
import           Compiler.Language.Coq.Base    as CoqBase

-- | Test group for all @Compiler.Converter.Renamer@ tests.
testRenamer :: Spec
testRenamer = describe "Compiler.Converter.Renamer" $ do
  testMustRenameIdent
  testRenameIdent

-------------------------------------------------------------------------------
-- Test identifiers                                                          --
-------------------------------------------------------------------------------

-- | Generator for arbitrary identifiers with optional number postfix.
genIdent :: Gen String
genIdent = do
  ident <- frequency
    [(6, genRegularIdent), (3, genKeyword), (1, genReservedIdent)]
  num <- choose (0, 42) :: Gen Int
  oneof [return ident, return (ident ++ show num)]

-- | Generator for arbitrary user defined identifiers.
genRegularIdent :: Gen String
genRegularIdent = oneof $ map return ["x", "y", "z"]

-- | Generator for arbitrary identifiers reserved by the Coq Base library.
genReservedIdent :: Gen String
genReservedIdent = oneof $ map return CoqBase.reservedIdents

-- | Generator for arbitrary Coq keywords.
genKeyword :: Gen String
genKeyword = oneof $ map return coqKeywords

-------------------------------------------------------------------------------
-- Tests for @mustRenameIdent@                                              --
-------------------------------------------------------------------------------

-- | Test group for 'mustRenameIdent' tests.
testMustRenameIdent :: Spec
testMustRenameIdent = describe "mustRenameIdent" $ do
  it "keywords must be renamed" $ do
    property $ forAll genKeyword $ mustRenameIdent emptyEnvironment
  it "reserved identifiers must be renamed" $ do
    property $ forAll genReservedIdent $ mustRenameIdent emptyEnvironment
  it "defined identifiers must be renamed" $ do
    property $ forAll genIdent $ \ident ->
      let env = define ident emptyEnvironment in mustRenameIdent env ident

-------------------------------------------------------------------------------
-- Tests for @renameIdent@                                                   --
-------------------------------------------------------------------------------

-- | Test group for 'renameIdent' tests.
testRenameIdent :: Spec
testRenameIdent = describe "renameIdent" $ do
  it "generated identifiers don't need to be renamed" $ do
    property $ forAll genIdent $ \ident ->
      let ident' = renameIdent emptyEnvironment ident
      in  not (mustRenameIdent emptyEnvironment ident')
  it "generated identifiers are not renamed again" $ do
    property $ forAll genIdent $ \ident ->
      let ident' = renameIdent emptyEnvironment ident
      in  renameIdent emptyEnvironment ident' == ident'
