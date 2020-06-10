-- | This module contains tests for 'FreeC.Pretty.Pretty' instances of IR AST
--   nodes.

module FreeC.IR.SyntaxTests
  ( testSyntax
  )
where

import           Test.Hspec

import           FreeC.IR.Syntax.ModuleTests

-- | Test group for 'FreeC.Pretty.Pretty' instances of IR AST nodes.
testSyntax :: Spec
testSyntax = do
  testModuleSyntax
