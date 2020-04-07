-- | This module contains a function for converting non-recursive
--   Haskell functions to Coq.

module FreeC.Backend.Coq.Converter.FuncDecl.NonRec
  ( convertNonRecFuncDecl
  )
where

import           FreeC.Backend.Coq.Converter.Expr
import           FreeC.Backend.Coq.Converter.FuncDecl.Common
import qualified FreeC.Backend.Coq.Syntax      as Coq
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter

-- | Converts a non-recursive Haskell function declaration to a Coq
--   @Definition@ sentence.
convertNonRecFuncDecl :: IR.FuncDecl -> Converter Coq.Sentence
convertNonRecFuncDecl funcDecl = localEnv $ do
  (qualid, binders, returnType') <- convertFuncHead funcDecl
  rhs'                           <- convertExpr (IR.funcDeclRhs funcDecl)
  return (Coq.definitionSentence qualid binders returnType' rhs')
