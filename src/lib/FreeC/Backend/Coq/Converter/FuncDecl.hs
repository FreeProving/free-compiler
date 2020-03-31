-- | This module contains functions for generating Coq function declarations
--   (in the form of @Definition@, @Fixpoint@ and @Section@ sentences) from
--   our intermediate representation.

module FreeC.Backend.Coq.Converter.FuncDecl where

import           Control.Monad.Extra            ( concatMapM )

import           FreeC.Backend.Coq.Converter.FuncDecl.NonRec
import           FreeC.Backend.Coq.Converter.FuncDecl.Rec
import qualified FreeC.Backend.Coq.Syntax      as G
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Monad.Converter

-- | Converts the given function declarations.
convertFuncDecls :: [HS.FuncDecl] -> Converter [G.Sentence]
convertFuncDecls funcDecls = do
  let components = groupFuncDecls funcDecls
  concatMapM convertFuncComponent components

-- | Converts a strongly connected component of the function dependency graph.
convertFuncComponent
  :: DependencyComponent HS.FuncDecl -> Converter [G.Sentence]
convertFuncComponent (NonRecursive decl) =
  return <$> convertNonRecFuncDecl decl
convertFuncComponent (Recursive decls) = convertRecFuncDecls decls
