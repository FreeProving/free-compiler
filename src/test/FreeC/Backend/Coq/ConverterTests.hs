module FreeC.Backend.Coq.ConverterTests where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.ExprTests
import           FreeC.Backend.Coq.Converter.FuncDeclTests
import           FreeC.Backend.Coq.Converter.TypeDeclTests
import           FreeC.Backend.Coq.Converter.TypeTests

-- | Test group for all @FreeC.Backend.Coq.Converter@ tests.
testConverter :: Spec
testConverter = do
  testConvertType
  testConvertTypeDecl
  testConvertDataDecls
  testConvertExpr
  testConvertFuncDecl
