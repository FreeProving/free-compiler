-- | This module contains a function for converting non-recursive
--   Haskell functions to Coq.

module Compiler.Backend.Coq.Converter.FuncDecl.NonRec
  ( convertNonRecFuncDecl
  )
where

import           Compiler.Backend.Coq.Converter.Expr
import           Compiler.Backend.Coq.Converter.FuncDecl.Common
import qualified Compiler.Backend.Coq.Syntax   as G
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Monad.Converter

-- | Converts a non-recursive Haskell function declaration to a Coq
--   @Definition@ sentence.
convertNonRecFuncDecl :: HS.FuncDecl -> Converter G.Sentence
convertNonRecFuncDecl funcDecl = localEnv $ do
  (qualid, binders, returnType') <- convertFuncHead funcDecl
  rhs'                           <- convertExpr (HS.funcDeclRhs funcDecl)
  return (G.definitionSentence qualid binders returnType' rhs')
