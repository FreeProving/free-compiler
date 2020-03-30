-- | This module contains a function for converting non-recursive
--   Haskell functions to Coq.

module FreeC.Backend.Coq.Converter.FuncDecl.NonRec
  ( convertNonRecFuncDecl
  )
where

import           FreeC.Backend.Coq.Converter.Expr
import           FreeC.Backend.Coq.Converter.FuncDecl.Common
import qualified FreeC.Backend.Coq.Syntax      as G
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Monad.Converter

-- | Converts a non-recursive Haskell function declaration to a Coq
--   @Definition@ sentence.
convertNonRecFuncDecl :: HS.FuncDecl -> Converter G.Sentence
convertNonRecFuncDecl funcDecl = localEnv $ do
  (qualid, binders, returnType') <- convertFuncHead funcDecl
  rhs'                           <- convertExpr (HS.funcDeclRhs funcDecl)
  return (G.definitionSentence qualid binders returnType' rhs')
