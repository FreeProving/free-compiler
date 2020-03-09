-- | This module contains a function for converting non-recursive
--   Haskell functions to Coq.

module Compiler.Converter.FuncDecl.NonRec
  ( convertNonRecFuncDecl
  )
where

import           Compiler.Converter.Expr
import           Compiler.Converter.FuncDecl.Common
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

-- | Converts a non-recursive Haskell function declaration to a Coq
--   @Definition@ sentence.
convertNonRecFuncDecl :: HS.FuncDecl -> Converter G.Sentence
convertNonRecFuncDecl (HS.FuncDecl _ (HS.DeclIdent _ ident) _ args expr _) =
  localEnv $ do
    -- TODO convert type arguments and return type from AST
    let name = HS.UnQual (HS.Ident ident)
    (qualid, binders, returnType') <- convertFuncHead name args
    expr'                          <- convertExpr expr
    return (G.definitionSentence qualid binders returnType' expr')
