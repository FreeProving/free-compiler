-- | This module contains functions to identify strongly connected components
--   of the dependency graph.
--
--   The dependency analysis is necessary because Coq does not allow functions
--   and data types to be used before they have been declared and we need to
--   identify (mutually) recursive functions.
--
--   The dependency analysis does not test whether there are undefined
--   identifiers. This is done by the converter.

module Compiler.Analysis.DependencyAnalysis
  ( DependencyComponent(..)
  , groupDependencies
  , groupTypeDecls
  , groupFuncDecls
  )
where

import           Data.Graph

import           Compiler.Analysis.DependencyGraph
import qualified Compiler.Haskell.AST          as HS

-- | A strongly connected component of the dependency graph.
--
--   All declarations that mutually depend on each other are in the same
--   strongly connected component.
--
--   The only difference to @'SCC' decl@ is that the constructors
--   have been renamed to be more explainatory in the context of dependency
--   analysis.
data DependencyComponent decl =
  NonRecursive decl   -- ^ A single non-recursive declaration.
  | Recursive [decl]  -- ^ A list of mutually recursive declarations.

-- | Converts a strongly connected component from @Data.Graph@ to a
--   'DependencyComponent'.
convertSCC :: SCC decl -> DependencyComponent decl
convertSCC (AcyclicSCC decl ) = NonRecursive decl
convertSCC (CyclicSCC  decls) = Recursive decls

-- | Computes the strongly connected components of the given dependency graph.
--
--   Each strongly connected component corresponds either to a set of mutually
--   recursive declarations or a single non-recursive declaration.
--
--   The returned list of strongly connected components is in reverse
--   topological order, i.e. a component @A@ precedes another component @B@ if
--   @A@ contains any declaration that depends on a declartion in $B$.
--   If two components do not depend on each other, they are in reverse
--   alphabetical order.
groupDependencies :: DependencyGraph decl -> [DependencyComponent decl]
groupDependencies = map convertSCC . stronglyConnComp . entries

-- | Combines the construction of the dependency graphs for the given
--   type declarations (See 'typeDependencyGraph') with the computaton of
--   strongly connected components.
groupTypeDecls :: [HS.TypeDecl] -> [DependencyComponent HS.TypeDecl]
groupTypeDecls decls = groupDependencies (typeDependencyGraph decls)

-- | Combines the construction of the dependency graphs for the given
--   function declarations (See 'funcDependencyGraph') with the computaton
--   of strongly connected components.
groupFuncDecls :: [HS.FuncDecl] -> [DependencyComponent HS.FuncDecl]
groupFuncDecls decls = groupDependencies (funcDependencyGraph decls)
