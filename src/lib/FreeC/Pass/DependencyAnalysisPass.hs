-- | This module contains a compiler pass that computes the strongly connected
--   components of either the function or type dependency graph and transforms
--   the strongly connected components using the given child passes.
--
--   = Example
--
--    If @pass1@, @pass2@ and @pass3@ are 'DependencyAwarePass'es for function
--    declarations, then @dependencyAnalysisPass [pass1, pass2, pass3]@ builds
--    a compiler pass that computes the strongly connected components of the
--    given modules function dependency graph. Each strongly connected component
--    is first transformed with @pass1@. The result is further processed by
--    @pass2@ and its result is passed to @pass3@. After all three passes have
--    been applied to the first strongly connected component, the subsequent
--    components are processed.
--
--   = Specification
--
--   == Preconditions
--
--   The preconditions of all child passes that are not already guaranteed by
--   preceding child passes should hold.
--
--   == Translation
--
--   The transformations of the child passes are applied.
--   Due to the computation of strongly connected components, the order of
--   declarations is changed. They are rearranged into reverse topological
--   order.
--
--   == Postconditions
--
--   The postconditions of all child passes that are not broken by subsequent
--   child passes hold.
--
--   == Error cases
--
--   The messages reported by the child passes are reported.
module FreeC.Pass.DependencyAnalysisPass
  ( DependencyAwarePass
  , dependencyAnalysisPass
  ) where

import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax as IR
import           FreeC.Monad.Converter
import           FreeC.Pass

-- | Type of a compiler 'Pass' that does not operate on entire modules but
--   on individual strongly connected components of the dependency graph
--   for declarations of type @decl@.
type DependencyAwarePass decl = Pass (DependencyComponent decl)

-- | Type class for declaration AST nodes whose dependencies can be analyzed.
class DependencyAnalysisPass decl where
  -- | Constructs the dependency graph for the given nodes.
  groupDecls :: [decl] -> [DependencyComponent decl]

  -- | Gets the declarations of the node type from the given module.
  getDecls :: IR.Module -> [decl]

  -- | Replaces the declarations of the node type in the given module.
  setDecls :: IR.Module -> [decl] -> IR.Module

-- | The dependencies of type declarations can be analyzed.
instance DependencyAnalysisPass IR.TypeDecl where
  groupDecls         = groupTypeDecls

  getDecls           = IR.modTypeDecls

  setDecls ast decls = ast { IR.modTypeDecls = decls }

-- | The dependencies of function declarations can be analyzed.
instance DependencyAnalysisPass IR.FuncDecl where
  groupDecls         = groupFuncDecls

  getDecls           = IR.modFuncDecls

  setDecls ast decls = ast { IR.modFuncDecls = decls }

-- | Applies the given child passes to the strongly connected components
--   of the dependency graph for declarations of type @decl@ of the given
--   module.
dependencyAnalysisPass
  :: DependencyAnalysisPass decl
  => [DependencyAwarePass decl] -> IR.Module -> Converter IR.Module
dependencyAnalysisPass = subPipelinePass getComponents setComponents
 where
   getComponents     = groupDecls . getDecls

   setComponents ast = setDecls ast . concatMap unwrapComponent
