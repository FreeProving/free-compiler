module FreeC.Backend.Coq.Converter.FuncDeclTests where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.FuncDecl.NonRecTests
import           FreeC.Backend.Coq.Converter.FuncDecl.RecTests

testConvertFuncDecl :: Spec
testConvertFuncDecl = describe "FreeC.Backend.Coq.Converter.FuncDecl" $ do
  testConvertNonRecFuncDecl
  testConvertRecFuncDecls
