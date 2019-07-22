-- | This module contains functions to construct dependency graphs of
--   Haskell modules. A dependency graph is a directed graph whose nodes
--   are labelled with declarations. There is an edge from node @A@ to @B@
--   if the declaration of @A@ depends on the declaration of @B@ (i.e. in Coq
--   @B@ has to be defined before @A@ or both have to be declared in the same
--   sentence).

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
  , DGNode
  , DGEntry
  , DependencyGraph(..)
  , errorKey
  , undefinedKey
  , entries
  , typeDependencyGraph
  , funcDependencyGraph
  )
where

import           Data.Graph
import           Data.Maybe                     ( catMaybes )
import qualified Data.Set                      as Set
import           Data.Tuple.Extra

import           Compiler.Analysis.DependencyExtraction
import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Dependency graph                                                          --
-------------------------------------------------------------------------------

-- | Every node of the dependency graph is uniquely identified by a key.
--   We use the Haskell identifiers and symbols to identify the nodes.
type DGKey = HS.Name

-- | The nodes of the dependency graph are Haskell declaraions.
type DGNode = HS.Decl

-- | Every node (declaration) in a dependency graph is associated with a
--   unique key (Haskell identifier) and a list of keys that identify the
--   nodes this node depends on (adjacency list).
type DGEntry = (DGNode, DGKey, [DGKey])

-- | A dependency graph is a directed graph whose nodes are Haskell
--   declarations (See 'DGNode'). There is an edge from node @A@ to
--   node @B@ if the declaration of @A@ depends on @B@.
--
--   Nodes are identified by their Haskell identifier (See 'DGKey').
--   Internally nodes are identified by a number (See 'Vertex').
--
--   In addition to the actual 'Graph' that stores the adjacency matrix
--   of the internal identifiers, this tuple contains functions to convert
--   between the internal and high level representation.
data DependencyGraph =
  DependencyGraph
    Graph                   -- ^ The actual graph.
    (Vertex -> DGEntry)     -- ^ Gets an entry for a vertex of the graph.
    (DGKey -> Maybe Vertex) -- ^ Gets the vertex of the node with the given key.

-------------------------------------------------------------------------------
-- Special keys                                                              --
-------------------------------------------------------------------------------

-- | The key that functions that use the `error "<message>"` error term depend
--   on.
errorKey :: DGKey
errorKey = HS.Ident "error"

-- | The key that functions that use the `undefined` error term depend on.
undefinedKey :: DGKey
undefinedKey = HS.Ident "undefined"

-------------------------------------------------------------------------------
-- Getters                                                                   --
-------------------------------------------------------------------------------

-- | Gets the entries of the given dependency graph.
entries :: DependencyGraph -> [DGEntry]
entries (DependencyGraph graph getEntry _) = map getEntry (vertices graph)

-------------------------------------------------------------------------------
-- Type dependencies                                                         --
-------------------------------------------------------------------------------

-- | Creates the dependency graph for a list of data type or type synonym
--   declarations.
--
--   If the given list contains other kinds of declarations, they are ignored.
typeDependencyGraph :: [HS.Decl] -> DependencyGraph
typeDependencyGraph =
  uncurry3 DependencyGraph . graphFromEdges . catMaybes . map typeDeclEntries

-- | Creates an entry of the dependency graph for the given data type or type
--   synonym declaration.
--
--   Returns @Nothing@ if the given declaration is not a data type or type
--   synonym declaration.
typeDeclEntries :: HS.Decl -> Maybe DGEntry
typeDeclEntries decl@(HS.TypeDecl _ (HS.DeclIdent _ ident) _ _) =
  Just (decl, HS.Ident ident, Set.toList (typeDeclDependencies decl))
typeDeclEntries decl@(HS.DataDecl _ (HS.DeclIdent _ ident) _ _) =
  Just (decl, HS.Ident ident, Set.toList (typeDeclDependencies decl))
typeDeclEntries _ = Nothing

-------------------------------------------------------------------------------
-- Function dependencies                                                     --
-------------------------------------------------------------------------------

-- | Creates the dependency graph for a list of function declarations.
--
--   If the given list contains other kinds of declarations, they are ignored.
funcDependencyGraph :: [HS.Decl] -> DependencyGraph
funcDependencyGraph =
  uncurry3 DependencyGraph . graphFromEdges . catMaybes . map funcDeclEntries

-- | Creates an entry of the dependency graph for the given function
--   declaration or pattern binding.
funcDeclEntries :: HS.Decl -> Maybe DGEntry
funcDeclEntries decl@(HS.FuncDecl _ (HS.DeclIdent _ ident) _ _) =
  Just (decl, HS.Ident ident, Set.toList (funcDeclDependencies decl))
funcDeclEntries _ = Nothing

-------------------------------------------------------------------------------
-- Pretty print dependency graph                                             --
-------------------------------------------------------------------------------

-- | Pretty instance that converts a dependency graph to the DOT format.
instance Pretty DependencyGraph where
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
       in  int v
           <+> brackets (label <> equals <> dquotes (prettyKey key))
           <>  semi

     -- | Pretty prints the key of a node.
     prettyKey :: DGKey -> Doc
     prettyKey (HS.Ident ident)   = prettyString ident
     prettyKey (HS.Symbol symbol) = parens (prettyString symbol)

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
