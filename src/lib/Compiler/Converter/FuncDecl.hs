-- | This module contains functions for converting function declarations from
--   Haskell to Coq.

module Compiler.Converter.FuncDecl where

import           Control.Monad.Extra            ( whenM
                                                , zipWithM_
                                                )

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.TypeInference
import           Compiler.Converter.FuncDecl.Common
import           Compiler.Converter.FuncDecl.NonRec
import           Compiler.Converter.FuncDecl.Rec
import           Compiler.Environment
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-- | Converts a strongly connected component of the function dependency graph.
convertFuncComponent
  :: DependencyComponent HS.FuncDecl -> Converter [G.Sentence]
convertFuncComponent (NonRecursive decl) = do
  inferAndInsertTypeSigs [decl]
  defineFuncDecl decl
  decl' <- convertNonRecFuncDecl decl
  return [decl']
convertFuncComponent (Recursive decls) = do
  inferAndInsertTypeSigs decls
  mapM_ defineFuncDecl decls
  convertRecFuncDecls decls

-- | Infers the types of the given function declarations and inserts type
--   signatures into the environment.
inferAndInsertTypeSigs :: [HS.FuncDecl] -> Converter ()
inferAndInsertTypeSigs funcDecls = do
  types <- inferFuncDeclTypes funcDecls
  zipWithM_ insertTypeSig funcDecls types

-- Inserts a type signature for a function declaration of the given type into
-- the environment.
insertTypeSig :: HS.FuncDecl -> HS.TypeSchema -> Converter ()
insertTypeSig funcDecl typeSchema = do
  let name = HS.UnQual (HS.Ident (HS.fromDeclIdent (HS.getDeclIdent funcDecl)))
  whenM (inEnv $ not . hasTypeSig name) $ modifyEnv $ defineTypeSig name
                                                                    typeSchema
