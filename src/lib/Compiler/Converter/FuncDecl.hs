-- | This module contains functions for converting function declarations from
--   Haskell to Coq.

module Compiler.Converter.FuncDecl where

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Converter.FuncDecl.Common
import           Compiler.Converter.FuncDecl.Rec
import           Compiler.Converter.FuncDecl.NonRec
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

-- | Converts a strongly connected component of the function dependency graph.
convertFuncComponent
  :: DependencyComponent HS.FuncDecl -> Converter [G.Sentence]
convertFuncComponent (NonRecursive decl) = do
  defineFuncDecl decl
  decl' <- convertNonRecFuncDecl decl
  return [decl']
convertFuncComponent (Recursive decls) = do
  mapM_ defineFuncDecl decls
  convertRecFuncDecls decls
