-- | This module contains a function for converting non-recursive
--   Haskell functions to Coq.
module FreeC.Backend.Coq.Converter.FuncDecl.NonRec
  ( convertNonRecFuncDecl
  , convertNonRecFuncDecls
  ) where

import           FreeC.Backend.Coq.Converter.Expr
import           FreeC.Backend.Coq.Converter.FuncDecl.Common
import qualified FreeC.Backend.Coq.Syntax                    as Coq
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax                             as IR
import           FreeC.Monad.Converter

-- | Converts non-recursive but possibly linear dependent Haskell functions
--   into an ordered list of @Definition@ sentences such that each definition
--   only depends on definitions at preceding list positions.
convertNonRecFuncDecls :: [ IR.FuncDecl ] -> Converter [ Coq.Sentence ]
convertNonRecFuncDecls decls
  = let orderedDecls = concatMap unwrapComponent
          (dependencyComponents (funcDependencyGraph decls))
    in mapM convertNonRecFuncDecl orderedDecls

-- | Converts a non-recursive Haskell function declaration to a Coq
--   @Definition@ sentence.
convertNonRecFuncDecl :: IR.FuncDecl -> Converter Coq.Sentence
convertNonRecFuncDecl funcDecl = localEnv
  $ do
    (qualid, binders, returnType') <- convertFuncHead funcDecl
    rhs' <- convertExpr (IR.funcDeclRhs funcDecl)
    return (Coq.definitionSentence qualid binders returnType' rhs')
