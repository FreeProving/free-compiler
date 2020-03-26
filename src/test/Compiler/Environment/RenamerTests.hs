module Compiler.Environment.RenamerTests where

import           Test.Hspec
import           Test.QuickCheck

import           Data.Maybe                     ( catMaybes )

import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Coq.Keywords
import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.Renamer
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Haskell.SrcSpan
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
    [ (6, genRegularIdent)
    , (2, genKeyword)
    , (2, genVernacularCommand)
    , (1, genReservedIdent)
    ]
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

-- | Generator for arbitrary Vernacular commands.
genVernacularCommand :: Gen String
genVernacularCommand = oneof $ map return vernacularCommands

-------------------------------------------------------------------------------
-- Tests for @mustRenameIdent@                                              --
-------------------------------------------------------------------------------

-- | Test group for 'mustRenameIdent' tests.
testMustRenameIdent :: Spec
testMustRenameIdent = describe "mustRenameIdent" $ do
  it "keywords must be renamed" $ do
    property $ forAll genKeyword $ flip mustRenameIdent emptyEnv
  it "reserved identifiers must be renamed" $ do
    property $ forAll genReservedIdent $ flip mustRenameIdent emptyEnv
  it "defined identifiers must be renamed" $ do
    property $ forAll genIdent $ \ident ->
      let env = addEntry
            TypeVarEntry { entrySrcSpan = NoSrcSpan
                         , entryName    = HS.UnQual (HS.Ident ident)
                         , entryIdent   = G.bare ident
                         }
            emptyEnv
      in  mustRenameIdent ident env

-------------------------------------------------------------------------------
-- Tests for @renameIdent@                                                   --
-------------------------------------------------------------------------------

-- | Test group for 'renameIdent' tests.
testRenameIdent :: Spec
testRenameIdent = describe "renameIdent" $ do
  it "generated identifiers don't need to be renamed" $ do
    property $ forAll genIdent $ \ident ->
      let ident' = renameIdent ident emptyEnv
      in  not (mustRenameIdent ident' emptyEnv)
  it "generated identifiers are not renamed again" $ do
    property $ forAll genIdent $ \ident ->
      let ident' = renameIdent ident emptyEnv
      in  renameIdent ident' emptyEnv == ident'

-------------------------------------------------------------------------------
-- Tests for @defineLocally@                                                 --
-------------------------------------------------------------------------------

-- | Test group for 'defineLocally' tests.
testDefineLocally :: Spec
testDefineLocally = describe "defineLocally" $ do
  it "detects redefinitions of data type declarations"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["data Foo = Foo", "data Foo = Bar"]

  it "detects redefinitions of type synonym declarations"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["type Foo = Integer", "type Foo a = [a]"]

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

  it "detects redefinitions of variables"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["data Foo a a = Foo a"]

  it "detects redefinitions of function declarations"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["foo = 42", "foo :: Integer", "foo = 1337"]

  it "detects redefinitions of function arguments"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls
        ["add :: Integer -> Integer -> Integer", "add x x = x + x"]

  it "detects redefinitions of constructor pattern arguments"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["head xs = case xs of {[] -> undefined; x:x -> x}"]

  it "allows to shadow variables " $ shouldSucceed $ fromConverter $ do
    _ <- convertTestDecls
      ["head :: [a] -> a", "head xs = case xs of {[] -> undefined; x:xs -> x}"]
    return (return ())
