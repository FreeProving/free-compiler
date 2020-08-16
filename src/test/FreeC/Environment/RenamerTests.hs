-- | This module contains tests for "FreeC.Environment.Renamer".
module FreeC.Environment.RenamerTests where

import           Data.Maybe                 ( mapMaybe )
import           Test.Hspec
import           Test.QuickCheck

import qualified FreeC.Backend.Coq.Base     as Coq.Base
import           FreeC.Backend.Coq.Keywords
import qualified FreeC.Backend.Coq.Syntax   as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.Renamer
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax            as IR

-- | Test group for all @FreeC.Environment.Renamer@ tests.
testRenamer :: Spec
testRenamer = describe "FreeC.Environment.Renamer" $ do
  testMustRenameIdent
  testRenameIdent

-------------------------------------------------------------------------------
-- Test identifiers                                                          --
-------------------------------------------------------------------------------
-- | Generator for arbitrary identifiers with optional number postfix.
genIdent :: Gen String
genIdent = do
  ident <- frequency [ (6, genRegularIdent)
                     , (2, genKeyword)
                     , (2, genVernacularCommand)
                     , (1, genReservedIdent)
                     ]
  num <- choose (0, 42) :: Gen Int
  oneof $ map return [ ident, ident ++ show num ]

-- | Generator for arbitrary user defined identifiers.
genRegularIdent :: Gen String
genRegularIdent = oneof $ map return [ "x", "y", "z" ]

-- | Generator for arbitrary identifiers reserved by the Coq Base library.
genReservedIdent :: Gen String
genReservedIdent
  = oneof $ map return $ mapMaybe Coq.unpackQualid Coq.Base.reservedIdents

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
      let env = addEntry TypeVarEntry
            { entrySrcSpan   = NoSrcSpan
            , entryName      = IR.UnQual (IR.Ident ident)
            , entryIdent     = Coq.bare ident
            , entryAgdaIdent = undefined -- ignore Agda identifiers for the moment - TODO: add Unit Tests for Agda renamer!
            } emptyEnv
      in mustRenameIdent ident env

-------------------------------------------------------------------------------
-- Tests for @renameIdent@                                                   --
-------------------------------------------------------------------------------
-- | Test group for 'renameIdent' tests.
testRenameIdent :: Spec
testRenameIdent = describe "renameIdent" $ do
  it "generated identifiers don't need to be renamed" $ do
    property $ forAll genIdent $ \ident ->
      let ident' = renameIdent ident emptyEnv
      in not (mustRenameIdent ident' emptyEnv)
  it "generated identifiers are not renamed again" $ do
    property $ forAll genIdent $ \ident ->
      let ident' = renameIdent ident emptyEnv
      in renameIdent ident' emptyEnv == ident'
