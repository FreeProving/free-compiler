-- | This module contains tests for modules with the
--   @FreeC.Backend.Agda@ prefix.
module FreeC.Backend.Agda.Tests ( testAgdaBackend ) where

import           Test.Hspec

import           FreeC.Backend.Agda.Converter.FuncDeclTests
import           FreeC.Backend.Agda.Converter.TypeDeclTests

-- | Test group for tests of modules with the @FreeC.Backend.Agda@ prefix.
testAgdaBackend :: Spec
testAgdaBackend = do
  testConvertDataDecls
  testConvertFuncDecls
