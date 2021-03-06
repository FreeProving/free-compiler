-- | This module contains functions to construct dependency graphs of
--   declarations and modules of the intermediate language. A dependency graph
--   is a directed graph whose nodes are labeled with declarations. There is an
--   edge from node @A@ to @B@ if the declaration of @A@ depends on the
--   declaration of @B@ (i.e. in Coq @B@ has to be defined before @A@ or both
--   have to be declared in the same sentence). The module dependency graph
--   contains an edge from node @A@ to @B@ if the module of @A@ contains an
--   @import@ declaration for the module of @B@.
--
--   The dependency graph does only contain defined top-level declarations
--   (i.e. there are no nodes for imported or built-in data types or operations
--   and there are no nodes for local variables such as function parameters or
--   variable patterns). However, the entries of the dependency graph contain
--   keys for predefined functions (but not local variables) as well as the
--   special functions @error@ and @undefined@ that are used in error terms.
--
--   We distinguish between the type and value dependency graph.
--   This is because function declarations and type declarations
--   live in separate scopes but we want to avoid name conflicts.
--   Since we assume all type declarations to precede function declarations
--   in the generated Coq code, this separation of the dependency graphs
--   should not be a problem. For the same reason, the value dependency
--   graph does not include nodes for constructors (as always, the keys of
--   used constructors are still present).
--
--   The construction of a dependency graph does not fail even if there are
--   are undefined identifiers. The dependency graph does not know about the
--   environment, it only knows which (type) constructors and (type) variables
--   occur freely in the declarations. Most importantly, that means that it
--   does not know about the module system. Thus, dependency analysis should
--   not be performed before all references have been resolved to their
--   original (qualified) identifiers.
--
--   For debugging purposes, dependency graphs can be converted to the DOT
--   format such that they can be visualized using Graphviz
--   (See <https://www.graphviz.org/>).
module FreeC.IR.DependencyGraph
  ( -- * Dependency Graph
    DGKey
  , DGEntry
  , DependencyGraph(..)
    -- ** Getters
  , dgEntries
    -- ** Predicates
  , dependsDirectlyOn
    -- ** Constructors
  , typeDependencyGraph
  , valueDependencyGraph
  , moduleDependencyGraph
    -- * Strongly Connected Components
  , DependencyComponent(..)
  , unwrapComponent
    -- ** Constructors
  , dependencyComponents
  , typeDependencyComponents
  , valueDependencyComponents
  , groupModules
    -- ** Manipulating
  , mapComponent
  , mapComponentM
  , mapComponentM_
  ) where

import           Control.Monad      ( liftM2, void )
import           Control.Monad.Fail ( MonadFail )
import           Data.Graph
import           Data.Maybe         ( mapMaybe )
import           Data.Tuple.Extra

import           FreeC.IR.Reference ( HasRefs, typeRefs, valueRefs )
import qualified FreeC.IR.Syntax    as IR
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Dependency Graph                                                          --
-------------------------------------------------------------------------------
-- | Every node of the dependency graph is uniquely identified by a key.
--   We use their qualified original name to identify declarations.
type DGKey = IR.QName

-- | Every node (i.e., declaration) in a dependency graph is associated with a
--   unique key (its qualified original name) and a list of keys that identify
--   the nodes this node depends on (adjacency list).
type DGEntry node = (node, DGKey, [DGKey])

-- | A dependency graph is a directed graph whose nodes are declarations
--   (Usually 'IR.TypeDecl' or 'IR.FuncDecl'). There is an edge from node
--   @A@ to node @B@ if the declaration of @A@ depends on @B@.
--
--   Nodes are identified by their qualified original name (See 'DGKey').
--   Internally, nodes are identified by a number (See 'Vertex').
--
--   In addition to the actual 'Graph' that stores the adjacency matrix
--   of the internal identifiers, this data type contains functions to convert
--   between the internal and high level representation.
data DependencyGraph node = DependencyGraph
  { dgGraph     :: Graph
    -- ^ The actual graph.
  , dgGetEntry  :: Vertex -> DGEntry node
    -- ^ Gets an entry for a vertex of the graph.
  , dgGetVertex :: DGKey -> Maybe Vertex
    -- ^ Gets the vertex of a node with the given key.
  }

-------------------------------------------------------------------------------
-- Getters                                                                   --
-------------------------------------------------------------------------------
-- | Gets the entries of the given dependency graph.
dgEntries :: DependencyGraph node -> [DGEntry node]
dgEntries = liftM2 map dgGetEntry dgVertices

-- | Gets the vertices of the given dependency graph.
dgVertices :: DependencyGraph node -> [Vertex]
dgVertices = vertices . dgGraph

-- | Gets the edges of the given dependency graph.
dgEdges :: DependencyGraph node -> [(Vertex, Vertex)]
dgEdges = edges . dgGraph

-------------------------------------------------------------------------------
-- Predicates                                                                --
-------------------------------------------------------------------------------
-- | Tests whether two nodes (identified by the given keys) of the dependency
--   graph depend on each other directly (i.e., there is an edge from the
--   first node to the second node).
--
--   Returns @False@ if one of the nodes does not exist.
dependsDirectlyOn :: DependencyGraph node -- ^ The dependency graph.
                  -> DGKey                -- ^ The key of the first node.
                  -> DGKey                -- ^ The key of the second node.
                  -> Bool
dependsDirectlyOn graph k1 k2 = containsEdge == Just True
 where
  containsEdge :: Maybe Bool
  containsEdge = do
    v1 <- dgGetVertex graph k1
    v2 <- dgGetVertex graph k2
    return ((v1, v2) `elem` dgEdges graph)

-------------------------------------------------------------------------------
-- Type Dependencies                                                         --
-------------------------------------------------------------------------------
-- | Creates the type dependency graph for a list of nodes.
typeDependencyGraph
  :: (HasRefs node, IR.HasDeclIdent node) => [node] -> DependencyGraph node
typeDependencyGraph = uncurry3 DependencyGraph . graphFromEdges . map typeEntry

-- | Creates an entry of the type dependency graph.
typeEntry :: (HasRefs node, IR.HasDeclIdent node) => node -> DGEntry node
typeEntry node = (node, IR.declQName node, typeRefs node)

-------------------------------------------------------------------------------
-- Function Dependencies                                                     --
-------------------------------------------------------------------------------
-- | Creates the dependency graph for a list of function declarations.
valueDependencyGraph
  :: (HasRefs node, IR.HasDeclIdent node) => [node] -> DependencyGraph node
valueDependencyGraph
  = uncurry3 DependencyGraph . graphFromEdges . map valueEntry

-- | Creates an entry of the dependency graph for the given function
--   declaration or pattern binding.
valueEntry :: (HasRefs node, IR.HasDeclIdent node) => node -> DGEntry node
valueEntry node = (node, IR.declQName node, valueRefs node)

-------------------------------------------------------------------------------
-- Module Dependencies                                                       --
-------------------------------------------------------------------------------
-- | Creates the dependency graph for the given modules.
moduleDependencyGraph
  :: [IR.ModuleOf decls] -> DependencyGraph (IR.ModuleOf decls)
moduleDependencyGraph
  = uncurry3 DependencyGraph . graphFromEdges . map moduleEntries

-- | Creates an entry of the dependency graph for the given module.
moduleEntries :: IR.ModuleOf decls -> DGEntry (IR.ModuleOf decls)
moduleEntries decl
  = ( decl
    , IR.UnQual (IR.Ident (IR.modName decl))
    , map (IR.UnQual . IR.Ident . IR.importName) (IR.modImports decl)
    )

-------------------------------------------------------------------------------
-- Pretty Print Dependency Graph                                             --
-------------------------------------------------------------------------------
-- | Pretty instance that converts a dependency graph to the DOT format.
instance Pretty (DependencyGraph node) where
  pretty (DependencyGraph graph getEntry getVertex) = digraph
    <+> braces (line <> indent 2 (vcat (nodeDocs ++ edgesDocs)) <> line)
    <> line
   where
    -- | A document for the DOT digraph keyword.
    digraph :: Doc
    digraph = prettyString "digraph"

    -- | A document for the DOT label attribute.
    label :: Doc
    label = prettyString "label"

    -- | A document for the DOT arrow symbol.
    arrow :: Doc
    arrow = prettyString "->"

    -- | Pretty printed DOT nodes for the dependency graph.
    nodeDocs :: [Doc]
    nodeDocs = map prettyNode (vertices graph)

    -- | Pretty prints the given vertex as a DOT command. The key of the node
    --   is used a the label.
    prettyNode :: Vertex -> Doc
    prettyNode v
      = let (_, key, _) = getEntry v
        in int v <+> brackets (label <> equals <> dquotes (pretty key)) <> semi

    -- | Pretty printed DOT edges for the dependency graph.
    edgesDocs :: [Doc]
    edgesDocs = mapMaybe prettyEdges (vertices graph)

    -- | Pretty prints all outgoing edges of the given vertex as a single
    --   DOT command. Returns 'Nothing' if the vertex is not incident to
    --   any edge.
    prettyEdges :: Vertex -> Maybe Doc
    prettyEdges v
      = let (_, _, neighbors) = getEntry v
        in case mapMaybe getVertex neighbors of
             [] -> Nothing
             vs -> Just
               $ int v
               <+> arrow
               <+> braces (cat (punctuate comma (map int vs))) <> semi

-------------------------------------------------------------------------------
-- Strongly Connected Components                                             --
-------------------------------------------------------------------------------
-- | A strongly connected component of the dependency graph.
--
--   All declarations that mutually depend on each other are in the same
--   strongly connected component.
--
--   The only difference to @'SCC' decl@ is that the constructors have been
--   renamed to be more explanatory in the context of dependency analysis.
data DependencyComponent decl
  = NonRecursive decl -- ^ A single non-recursive declaration.
  | Recursive [decl]  -- ^ A list of mutually recursive declarations.
 deriving Show

-- | Gets the declarations wrapped by the given strongly connected component.
unwrapComponent :: DependencyComponent decl -> [decl]
unwrapComponent (NonRecursive decl) = [decl]
unwrapComponent (Recursive decls)   = decls

-------------------------------------------------------------------------------
-- Constructing SCCs                                                         --
-------------------------------------------------------------------------------
-- | Computes the strongly connected components of the given dependency graph.
--
--   Each strongly connected component corresponds either to a set of mutually
--   recursive declarations or a single non-recursive declaration.
--
--   The returned list of strongly connected components is in reverse
--   topological order, i.e. if any declaration in a strongly connected
--   component @B@ depends on a declaration in a strongly connected component
--   @A@, then @A@ precedes @B@ in the returned list.
--
--   If two components do not depend on each other, they are in reverse
--   alphabetical order.
dependencyComponents :: DependencyGraph a -> [DependencyComponent a]
dependencyComponents = map convertSCC . stronglyConnComp . dgEntries
 where
  -- | Converts a strongly connected component from @Data.Graph@ to a
  --   'DependencyComponent'.
  convertSCC :: SCC decl -> DependencyComponent decl
  convertSCC (AcyclicSCC decl) = NonRecursive decl
  convertSCC (CyclicSCC decls) = Recursive decls

-- | Combines the construction of the type dependency graph with the
--   computation of strongly connected components.
typeDependencyComponents :: (HasRefs node, IR.HasDeclIdent node)
                         => [node]
                         -> [DependencyComponent node]
typeDependencyComponents = dependencyComponents . typeDependencyGraph

-- | Combines the construction of the value dependency graph with the
--   computation of strongly connected components.
valueDependencyComponents :: (HasRefs node, IR.HasDeclIdent node)
                          => [node]
                          -> [DependencyComponent node]
valueDependencyComponents = dependencyComponents . valueDependencyGraph

-- | Combines the construction of the dependency graph for the given
--   modules (See 'moduleDependencyGraph') with the computation of strongly
--   connected components.
--
--   Since cyclic module dependencies are not allowed, all
--   'DependencyComponent's in the returned list should be 'NonRecursive'.
--   Otherwise, there is a module dependency error.
groupModules :: [IR.ModuleOf decls]
             -> [DependencyComponent (IR.ModuleOf decls)]
groupModules = dependencyComponents . moduleDependencyGraph

-------------------------------------------------------------------------------
-- Manipulating SCCs                                                         --
-------------------------------------------------------------------------------
-- | Applies the given function to the declarations in the given strongly
--   connected component of the dependency graph.
--
--   In case of a 'NonRecursive' component, the function is given a singleton
--   list. The given function must not change the number of declarations in the
--   component.
mapComponent :: ([decl] -> [decl'])
             -> DependencyComponent decl
             -> DependencyComponent decl'
mapComponent f (NonRecursive decl) = let [decl'] = f [decl]
                                     in NonRecursive decl'
mapComponent f (Recursive decls)   = Recursive (f decls)

-- | Monadic version of 'mapComponent'.
--
--   There must be a 'MonadFail' instance since this function fails if the
--   given function changes the number of declarations in a non-recursive
--   strongly connected component.
mapComponentM :: MonadFail m
              => ([decl] -> m [decl'])
              -> DependencyComponent decl
              -> m (DependencyComponent decl')
mapComponentM f (NonRecursive decl) = do
  [decl'] <- f [decl]
  return (NonRecursive decl')
mapComponentM f (Recursive decls)   = Recursive <$> f decls

-- | Like 'mapComponentM' but discards the result.
mapComponentM_
  :: MonadFail m => ([decl] -> m a) -> DependencyComponent decl -> m ()
mapComponentM_ f (NonRecursive decl) = void (f [decl])
mapComponentM_ f (Recursive decls)   = void (f decls)

-------------------------------------------------------------------------------
-- Pretty Print SCCs                                                         --
-------------------------------------------------------------------------------
-- | Pretty instance that pretty prints the declarations of a strongly
--   connected component.
--
--   Each declaration is on its own line and indented by two spaces.
--   The first line of the document indicates whether the component
--   was recursive or not.
instance Pretty decl => Pretty (DependencyComponent decl) where
  pretty (NonRecursive decl) = prettyString "non-recursive"
    <$$> indent 2 (pretty decl)
  pretty (Recursive decls)   = prettyString "recursive"
    <$$> indent 2 (vcat (map pretty decls))
