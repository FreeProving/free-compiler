module Compiler.Environment.RenamerTests where

import           Test.Hspec
import           Test.QuickCheck

import           Data.Maybe                     ( catMaybes )

import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Coq.Keywords
import           Compiler.Environment
import           Compiler.Environment.Renamer
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Util.Test

-- | Test group for all @Compiler.Environment.Renamer@ tests.
testRenamer :: Spec
testRenamer = describe "Compiler.Environment.Renamer" $ do
  testMustRenameIdent
  testRenameIdent
  testDefineLocally

-------------------------------------------------------------------------------
-- Test identifiers                                                          --
-------------------------------------------------------------------------------

-- | Generator for arbitrary identifiers with optional number postfix.
genIdent :: Gen String
genIdent = do
  ident <- frequency
    [(6, genRegularIdent), (3, genKeyword), (1, genReservedIdent)]
  num <- choose (0, 42) :: Gen Int
  oneof $ map return [ident, (ident ++ show num)]

-- | Generator for arbitrary user defined identifiers.
genRegularIdent :: Gen String
genRegularIdent = oneof $ map return ["x", "y", "z"]

-- | Generator for arbitrary identifiers reserved by the Coq Base library.
genReservedIdent :: Gen String
genReservedIdent =
  oneof $ map return $ catMaybes $ map (G.unpackQualid) CoqBase.reservedIdents

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
    property $ forAll genKeyword $ flip mustRenameIdent emptyEnvironment
  it "reserved identifiers must be renamed" $ do
    property $ forAll genReservedIdent $ flip mustRenameIdent emptyEnvironment
  it "defined identifiers must be renamed" $ do
    property $ forAll genIdent $ \ident ->
      let env = defineTypeVar (HS.Ident ident) (G.bare ident) emptyEnvironment
      in  mustRenameIdent ident env

-------------------------------------------------------------------------------
-- Tests for @renameIdent@                                                   --
-------------------------------------------------------------------------------

-- | Test group for 'renameIdent' tests.
testRenameIdent :: Spec
testRenameIdent = describe "renameIdent" $ do
  it "generated identifiers don't need to be renamed" $ do
    property $ forAll genIdent $ \ident ->
      let ident' = renameIdent ident emptyEnvironment
      in  not (mustRenameIdent ident' emptyEnvironment)
  it "generated identifiers are not renamed again" $ do
    property $ forAll genIdent $ \ident ->
      let ident' = renameIdent ident emptyEnvironment
      in  renameIdent ident' emptyEnvironment == ident'

-------------------------------------------------------------------------------
-- Tests for @defineLocally@                                                 --
-------------------------------------------------------------------------------

-- | Test group for 'defineLocally' tests.
testDefineLocally :: Spec
testDefineLocally = describe "defineLocally" $ do
  it "detects redefinitions of function declarations"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["foo = 42", "foo :: Int", "foo = 1337"]

  it "detects redefinitions of data type declarations"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["data Foo = Foo", "data Foo = Bar"]

  it "detects redefinitions of constructor declarations"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["data Foo = Foo | Foo"]

  it "detects redefinitions of constructor declarations"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["data Foo = Foo", "data Bar = Foo"]

  it "detects redefinitions of type variables"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["data Foo a a = Foo a"]
