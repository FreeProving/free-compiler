-- | This module contains tests for modules that are defined below @FreeC.IR@.

module FreeC.IR.Tests
  ( testIR
  )
where

import           Test.Hspec

import           FreeC.IR.InliningTests
import           FreeC.IR.ReferenceTests
import           FreeC.IR.SimilarTests
import           FreeC.IR.SubstTests
import           FreeC.IR.SubtermTests
import           FreeC.IR.SyntaxTests
import           FreeC.IR.TypeSynExpansionTests
import           FreeC.IR.UnificationTests

-- | Test group for tests of modules below @FreeC.IR@.
testIR :: Spec
testIR = do
  testInlining
  testReference
  testSimilar
  testExprSubst
  testSubterm
  testSyntax
  testTypeSynExpansion
  testUnification
