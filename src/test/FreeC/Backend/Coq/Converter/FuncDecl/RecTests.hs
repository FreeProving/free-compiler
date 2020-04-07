-- | This module contains tests for "FreeC.Backend.Coq.Converter.FuncDecl.Rec".

module FreeC.Backend.Coq.Converter.FuncDecl.RecTests
  ( testConvertRecFuncDecls
  )
where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithHelpersTests
import           FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithSectionsTests

-- | Test group for 'convertRecFuncDecls' tests.
testConvertRecFuncDecls :: Spec
testConvertRecFuncDecls = context "recursive functions" $ do
  testConvertRecFuncDeclWithHelpers
  testConvertRecFuncDeclWithSections
