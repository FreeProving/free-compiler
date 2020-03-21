-- | This module contains a compiler pass that infers the types of all
--   function declarations including the types of the sub-expressions of
--   their right-hand sides and type arguments to pass to used functions and
--   constructors.
--
--   TODO write documentation and examples

module Compiler.Pass.TypeInferencePass
  ( typeInferencePass
  )
where

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyGraph
import           Compiler.Analysis.TypeInference
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter
import           Compiler.Pass

-- | Applies 'inferFuncDeclComponentTypes' to all strongly connected components
--   of the function dependency graph of the given module.
typeInferencePass :: Pass HS.Module
typeInferencePass ast = do
  let modName         = HS.modName ast
      funcDecls       = HS.modFuncDecls ast
      dependencyGraph = funcDependencyGraph modName funcDecls
      components      = groupDependencies dependencyGraph
  components' <- inferFuncDeclComponentTypes components
  return ast { HS.modFuncDecls = concatMap unwrapComponent components' }
