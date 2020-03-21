-- | This module contains functions to construct dependency graphs of
--   Haskell declarations and modules. A dependency graph is a directed
--   graph whose nodes are labelled with declarations. There is an edge
--   from node @A@ to @B@ if the declaration of @A@ depends on the declaration
--   of @B@ (i.e. in Coq @B@ has to be defined before @A@ or both have to be
--   declared in the same sentence). The module dependency graph contains an
--   edge from node @A@ to @B@ if the module of @A@ contains an @import@
--   declaration for the module of @B@.

--   The dependency graph does only contain global, user defined declarations
--   (i.e. there are no nodes for build-in data types or operations and there
--   are no nodes for local variables such as function parameters or variable
--   patterns). However the entries of the dependency graph contain keys
--   for predefined functions (but not local vaiables) and the special
--   functions `error` and `undefined` that are used in error terms.
--
--   We distinguish between the type and function dependency graph.
--   This is because in Haskell function declarations and type declarations
--   live in separate scopes and we want to avoid name conflicts.
--   Because we assume all type declarations to preceed function declarations
--   in the generated Coq code, this should not be a problem. For the same
--   reason the function dependency graph does not include nodes for
--   constructors (as always, the keys of used constructors are still present).
--
--   The construction of a dependency graph does not fail even if there are
--   are undefined identifiers.
--
--   For debugging purposes dependency graphs can be converted to the DOT
--   format such that they can be visualized using Graphviz
--   (See <https://www.graphviz.org/>).

module Compiler.Analysis.DependencyGraph
  ( DGKey
  , DGEntry
  , DependencyGraph(..)
    -- * Getters
  , dependencyGraphEntries
    -- * Predicates
  , dependsDirectlyOn
    -- * Constructors
  , typeDependencyGraph
  , funcDependencyGraph
  , moduleDependencyGraph
  )
where

import           Data.Composition               ( (.:) )
import           Data.Graph
import           Data.Maybe                     ( catMaybes
                                                , fromMaybe
                                                )
import qualified Data.Set                      as Set
import           Data.Tuple.Extra

import           Compiler.Analysis.DependencyExtraction
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Dependency graph                                                          --
-------------------------------------------------------------------------------

-- | Every node of the dependency graph is uniquely identified by a key.
--   We use the Haskell identifiers and symbols to identify the nodes.
type DGKey = HS.QName

-- | Every node (declaration) in a dependency graph is associated with a
--   unique key (Haskell identifier) and a list of keys that identify the
--   nodes this node depends on (adjacency list).
type DGEntry node = (node, DGKey, [DGKey])

-- | A dependency graph is a directed graph whose nodes are Haskell
--   declarations (Usually 'HS.TypeDecl' or 'HS.FuncDecl'). There is an edge
--   from node @A@ to node @B@ if the declaration of @A@ depends on @B@.
--
--   Nodes are identified by their Haskell identifier (See 'DGKey').
--   Internally nodes are identified by a number (See 'Vertex').
--
--   In addition to the actual 'Graph' that stores the adjacency matrix
--   of the internal identifiers, this tuple contains functions to convert
--   between the internal and high level representation.
data DependencyGraph node =
  DependencyGraph
    Graph                    -- ^ The actual graph.
    (Vertex -> DGEntry node) -- ^ Gets an entry for a vertex of the graph.
    (DGKey -> Maybe Vertex)  -- ^ Gets the vertex of a node with the given key.

-------------------------------------------------------------------------------
-- Getters                                                                   --
-------------------------------------------------------------------------------

-- | Gets the entries of the given dependency graph.
dependencyGraphEntries :: DependencyGraph node -> [DGEntry node]
dependencyGraphEntries (DependencyGraph graph getEntry _) =
  map getEntry (vertices graph)

-------------------------------------------------------------------------------
-- Predicates                                                                --
-------------------------------------------------------------------------------

-- | Tests whether two nodes (identified by the given keys) of the dependency
--   graph depend on each other directly (i.e., there is an edge from the
--   first node to the second node).
--
--   Returns @False@ if one of the nodes does not exist.
dependsDirectlyOn
  :: DependencyGraph node -- ^ The dependency graph.
  -> DGKey                -- ^ The key of the first node.
  -> DGKey                -- ^ The key of the second node.
  -> Bool
dependsDirectlyOn (DependencyGraph graph _ getVertex) k1 k2 =
  fromMaybe False $ do
    v1 <- getVertex k1
    v2 <- getVertex k2
    return ((v1, v2) `elem` (edges graph))

-------------------------------------------------------------------------------
-- Type dependencies                                                         --
-------------------------------------------------------------------------------

-- | Creates the dependency graph for a list of data type or type synonym
--   declarations.
--
--   If the given list contains other kinds of declarations, they are ignored.
typeDependencyGraph
  :: HS.ModName    -- ^ The name of the module that contains the declarations.
  -> [HS.TypeDecl] -- ^ The declarations to create the dependency graph for.
  -> DependencyGraph HS.TypeDecl
typeDependencyGraph =
  uncurry3 DependencyGraph . graphFromEdges .: map . typeDeclEntry

-- | Creates an entry of the dependency graph for the given data type or type
--   synonym declaration.
typeDeclEntry
  :: HS.ModName  -- ^ The name of the module that contains the declaration.
  -> HS.TypeDecl -- ^ The declaration to create an entry for.
  -> DGEntry HS.TypeDecl
typeDeclEntry modName decl =
  ( decl
  , HS.typeDeclQName decl
  , Set.toList $ Set.map (unqualify modName) (typeDeclDependencySet decl)
  )

-------------------------------------------------------------------------------
-- Function dependencies                                                     --
-------------------------------------------------------------------------------

-- | Creates the dependency graph for a list of function declarations.
--
--   If the given list contains other kinds of declarations, they are ignored.
funcDependencyGraph
  :: HS.ModName    -- ^ The name of the module that contains the declarations.
  -> [HS.FuncDecl] -- ^ The declarations to create the dependency graph for.
  -> DependencyGraph HS.FuncDecl
funcDependencyGraph =
  uncurry3 DependencyGraph . graphFromEdges .: map . funcDeclEntry

-- | Creates an entry of the dependency graph for the given function
--   declaration or pattern binding.
funcDeclEntry
  :: HS.ModName  -- ^ The name of the module that contains the declaration.
  -> HS.FuncDecl -- ^ The declaration to create an entry for.
  -> DGEntry HS.FuncDecl
funcDeclEntry modName decl =
  ( decl
  , HS.funcDeclQName decl
  , Set.toList $ Set.map (unqualify modName) (funcDeclDependencySet decl)
  )

-------------------------------------------------------------------------------
-- Module dependencies                                                       --
-------------------------------------------------------------------------------

-- | Creates the dependency graph for a list of Haskell modules.
--
--   Modules without a name are excluded from the dependency graph.
moduleDependencyGraph :: [HS.Module] -> DependencyGraph HS.Module
moduleDependencyGraph =
  uncurry3 DependencyGraph . graphFromEdges . map moduleEntries

-- | Creates an entry of the dependency graoh for the given module.
--
--   The module must have a name, otherwise @Nothing@ is returned.
moduleEntries :: HS.Module -> DGEntry HS.Module
moduleEntries decl =
  ( decl
  , HS.UnQual (HS.Ident (HS.modName decl))
  , map (HS.UnQual . HS.Ident) (moduleDependencies decl)
  )

-------------------------------------------------------------------------------
-- Utility functions                                                         --
-------------------------------------------------------------------------------

-- | Converts names that are qualified with the given module name to an
--   unqualified name and leaves all other names unchanged.
unqualify :: HS.ModName -> HS.QName -> HS.QName
unqualify modName (HS.Qual modName' name) | modName == modName' = HS.UnQual name
unqualify _ name = name

-------------------------------------------------------------------------------
-- Pretty print dependency graph                                             --
-------------------------------------------------------------------------------

-- | Pretty instance that converts a dependency graph to the DOT format.
instance Pretty (DependencyGraph node) where
  pretty (DependencyGraph graph getEntry getVertex) =
    digraph
      <+> braces (line <> indent 2 (vcat (nodeDocs ++ edgesDocs)) <> line)
      <>  line
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
    prettyNode v =
      let (_, key, _) = getEntry v
      in  int v <+> brackets (label <> equals <> dquotes (pretty key)) <> semi

    -- | Pretty printed DOT edges for the dependency graph.
    edgesDocs :: [Doc]
    edgesDocs = catMaybes (map prettyEdges (vertices graph))

    -- | Pretty prints all outgoing edges of the given vertex as a single
    --   DOT command. Returns `Nothing` if the vertex is not incident to
    --   any edge.
    prettyEdges :: Vertex -> Maybe Doc
    prettyEdges v =
      let (_, _, neighbors) = getEntry v
      in  case catMaybes (map getVertex neighbors) of
            [] -> Nothing
            vs ->
              Just
                $   int v
                <+> arrow
                <+> braces (cat (punctuate comma (map int vs)))
                <>  semi
