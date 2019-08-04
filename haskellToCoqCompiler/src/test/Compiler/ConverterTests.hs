module Compiler.ConverterTests where

import           Test.Hspec

import Compiler.Converter.ExprTests
import Compiler.Converter.FuncDeclTests
import Compiler.Converter.TypeDeclTests
import Compiler.Converter.TypeTests

-- | Test group for all @Compiler.Converter@ tests.
testConverter :: Spec
testConverter = do
  testConvertType
  testConvertTypeDecl
  testConvertDataDecls
  testConvertExpr
  testConvertNonRecFuncDecl
  testConvertRecFuncDecls
