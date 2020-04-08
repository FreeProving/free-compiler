-- | This module contains tests for "FreeC.Backend.Coq.Converter.FuncDecl".

module FreeC.Backend.Coq.Converter.FuncDeclTests where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.FuncDecl.NonRecTests
import           FreeC.Backend.Coq.Converter.FuncDecl.RecTests

-- | Test group for "FreeC.Backend.Coq.Converter.FuncDecl" tests.
testConvertFuncDecl :: Spec
testConvertFuncDecl = describe "FreeC.Backend.Coq.Converter.FuncDecl" $ do
  testConvertNonRecFuncDecl
  testConvertRecFuncDecls
