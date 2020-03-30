-- | This module contains functions for generating Coq function declarations
--   (in the form of @Definition@, @Fixpoint@ and @Section@ sentences) from
--   our intermediate representation.

module Compiler.Backend.Coq.Converter.FuncDecl where

import           Control.Monad.Extra            ( concatMapM )

import           Compiler.Backend.Coq.Converter.FuncDecl.NonRec
import           Compiler.Backend.Coq.Converter.FuncDecl.Rec
import           Compiler.Backend.Coq.Converter.QuickCheck
import qualified Compiler.Backend.Coq.Syntax   as G
import           Compiler.IR.DependencyGraph
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Monad.Converter

-- | Converts the given function declarations.
convertFuncDecls :: [HS.FuncDecl] -> Converter [G.Sentence]
convertFuncDecls funcDecls = do
  -- Filter QuickCheck properties.
  let components = groupFuncDecls funcDecls
  (properties, funcComponents) <- filterQuickCheckProperties components

  -- Convert function declarations and QuickCheck properties.
  funcDecls' <- concatMapM convertFuncComponent funcComponents
  properties' <- concatMapM convertQuickCheckProperty properties
  return
    (  funcDecls'
    ++ [ G.comment "QuickCheck properties" | not (null properties') ]
    ++ properties'
    )

-- | Converts a strongly connected component of the function dependency graph.
convertFuncComponent
  :: DependencyComponent HS.FuncDecl -> Converter [G.Sentence]
convertFuncComponent (NonRecursive decl) =
  return <$> convertNonRecFuncDecl decl
convertFuncComponent (Recursive decls) = convertRecFuncDecls decls
