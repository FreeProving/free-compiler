module Compiler.Backend.Coq.ConverterTests where

import           Test.Hspec

import           Compiler.Backend.Coq.Converter.ExprTests
import           Compiler.Backend.Coq.Converter.FuncDeclTests
import           Compiler.Backend.Coq.Converter.ModuleTests
import           Compiler.Backend.Coq.Converter.QuickCheckTests
import           Compiler.Backend.Coq.Converter.TypeDeclTests
import           Compiler.Backend.Coq.Converter.TypeTests

-- | Test group for all @Compiler.Backend.Coq.Converter@ tests.
testConverter :: Spec
testConverter = do
  testConvertType
  testConvertTypeDecl
  testConvertDataDecls
  testConvertExpr
  testConvertNonRecFuncDecl
  testConvertRecFuncDeclsWithHelpers
  testConvertRecFuncDeclsWithSections
  testConvertQuickCheckProperty
  testConvertModule
