-- | This module contains functions to identify strongly connected components
--   of the dependency graph.
--
--   The dependency analysis is necessary because Coq does not allow functions
--   and data types to be used before they have been declared and we need to
--   identify (mutually) recursive functions. It is also used to translate
--   modules in the right order.
--
--   The dependency analysis does not test whether there are undefined
--   identifiers. This is done by the converter.

module Compiler.Analysis.DependencyAnalysis
  ( DependencyComponent(..)
  , mapComponent
  , mapComponentM
  , mapComponentM_
  , groupDependencies
  , groupTypeDecls
  , groupFuncDecls
  , groupModules
  )
where

import           Control.Monad.Fail             ( MonadFail )
import           Data.Composition               ( (.:) )
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
data DependencyComponent decl
  = NonRecursive decl -- ^ A single non-recursive declaration.
  | Recursive [decl]  -- ^ A list of mutually recursive declarations.

-- | Applies the given function to the declarations in the given strongly
--   connected component of the dependency graph.
--
--   In case of a 'NonRecursive' component, the function is given a singleton
--   list. The given must not change the number of declarations in the
--   component.
mapComponent
  :: ([decl] -> [decl'])
  -> DependencyComponent decl
  -> DependencyComponent decl'
mapComponent f (NonRecursive decl) =
  let [decl'] = f [decl] in NonRecursive decl'
mapComponent f (Recursive decls) = Recursive (f decls)

-- | Monadic version of 'mapComponent'.
mapComponentM
  :: MonadFail m
  => ([decl] -> m [decl'])
  -> DependencyComponent decl
  -> m (DependencyComponent decl')
mapComponentM f (NonRecursive decl) = do
  [decl'] <- f [decl]
  return (NonRecursive decl')
mapComponentM f (Recursive decls) = Recursive <$> f decls

-- | Like 'mapComponentM' but discards the result.
mapComponentM_
  :: MonadFail m => ([decl] -> m a) -> DependencyComponent decl -> m ()
mapComponentM_ f (NonRecursive decl ) = f [decl] >> return ()
mapComponentM_ f (Recursive    decls) = f decls >> return ()

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
groupDependencies = map convertSCC . stronglyConnComp . dependencyGraphEntries

-- | Combines the construction of the dependency graphs for the given
--   type declarations (See 'typeDependencyGraph') with the computation of
--   strongly connected components.
groupTypeDecls
  :: HS.ModName    -- ^ The name of the module that contains the declarations.
  -> [HS.TypeDecl] -- ^ The declarations to group.
  -> [DependencyComponent HS.TypeDecl]
groupTypeDecls = groupDependencies .: typeDependencyGraph

-- | Combines the construction of the dependency graphs for the given
--   function declarations (See 'funcDependencyGraph') with the computation
--   of strongly connected components.
groupFuncDecls
  :: HS.ModName    -- ^ The name of the module that contains the declarations.
  -> [HS.FuncDecl] -- ^ The declarations to group.
  -> [DependencyComponent HS.FuncDecl]
groupFuncDecls = groupDependencies .: funcDependencyGraph

-- | Combines the construction of the dependency graph for the given
--   Haskell modules (See 'moduleDependencyGraph') with the computation
--   of strongly connected components.
--
--   Since cyclic module dependencies are not allowed, all
--   'DependencyComponent's in the returned list should be 'NonRecursive'.
--   Otherwise there is a module dependency error.
groupModules :: [HS.Module] -> [DependencyComponent HS.Module]
groupModules = groupDependencies . moduleDependencyGraph
