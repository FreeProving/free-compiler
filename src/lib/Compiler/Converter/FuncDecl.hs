-- | This module contains functions for converting function declarations from
--   Haskell to Coq.

module Compiler.Converter.FuncDecl where

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Converter.FuncDecl.Common
import           Compiler.Converter.FuncDecl.NonRec
import           Compiler.Converter.FuncDecl.Rec
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

-- | Converts a strongly connected component of the function dependency graph.
convertFuncComponent
  :: DependencyComponent HS.FuncDecl -> Converter [G.Sentence]
convertFuncComponent (NonRecursive decl) = do
  [decl'] <- inferAndInsertTypeSigs [decl]
  defineFuncDecl decl'
  return <$> convertNonRecFuncDecl decl'
convertFuncComponent (Recursive decls) = do
  decls' <- inferAndInsertTypeSigs decls
  mapM_ defineFuncDecl decls'
  convertRecFuncDecls decls'
