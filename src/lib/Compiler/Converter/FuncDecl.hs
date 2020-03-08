-- | This module contains functions for converting function declarations from
--   Haskell to Coq.

module Compiler.Converter.FuncDecl where

import           Control.Monad.Extra            ( concatMapM )

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyGraph
import           Compiler.Converter.FuncDecl.Common
import           Compiler.Converter.FuncDecl.NonRec
import           Compiler.Converter.FuncDecl.Rec
import           Compiler.Converter.QuickCheck
import           Compiler.Environment
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

-- | Converts the given function declarations.
convertFuncDecls :: [HS.FuncDecl] -> Converter [G.Sentence]
convertFuncDecls funcDecls = do
  modName <- inEnv envModName
  let dependencyGraph = funcDependencyGraph modName funcDecls
      components      = groupDependencies dependencyGraph

  -- Infer types.
  components' <- flip mapM components $ \component -> do
    component' <- inferAndInsertTypeSigs component
    case component' of
      NonRecursive decl -> defineFuncDecl decl
      Recursive decls -> mapM_ defineFuncDecl decls
    return component'

  -- Filter QuickCheck properties.
  (properties, funcComponents) <- filterQuickCheckProperties components'

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