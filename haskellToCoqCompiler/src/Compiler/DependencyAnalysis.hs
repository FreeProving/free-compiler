-- | This module contains functions to construct dependency graphs of
--   Haskell modules. A dependency graph is a directed graph whose nodes
--   are labelled with declarations. There is an edge from node @A@ to @B@
--   if the declaration of @A@ depends on the declaration of @B@ (i.e. in Coq
--   @B@ has to be defined before @A@ or both have to be declared in the same
--   sentence). The dependency graph does only contain global, user defined
--   declarations (i.e. there are no nodes for build in data types or
--   operations and there are no nodes for local variables such as function
--   parameters or variable patterns)
--
--   The dependency analysis is necessary because Coq does not allow functions
--   and data types to be used before they have been declared and we need to
--   identify (mutually) recursive functions.
--
--   We distinguish between the type and function dependency graph.
--   This is because in Haskell function declarations and type declarations
--   live in separate scopes and we want to avoid name conflicts.
--   Because we assume all type declarations to preceed function declarations
--   in the generated Coq code, this should not be a problem. For the same
--   reason the function dependency graph does not include nodes for
--   constructor (the keys of used constructors are still present).
--
--   The dependency analysis does not yet test whether there are undefined
--   identifiers.
--
--   For debugging purposes dependency graphs can be converted to the DOT
--   format such that they can be visualized using Graphviz
--   (See <https://www.graphviz.org/>).

module Compiler.DependencyAnalysis
  ( DependencyGraph
  , DependencyComponent(..)
  , groupDependencies
  , groupDeclarations
  , typeDependencyGraph
  , funcDependencyGraph
  )
where

import           Data.Graph
import           Data.Maybe                     ( catMaybes )
import           Data.Set                       ( Set
                                                , (\\)
                                                )
import qualified Data.Set                      as Set

import           Text.PrettyPrint.Leijen.Text

import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.Pretty
import           Compiler.Util.Data.Tuple

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
  DependencyGraph Graph (Vertex -> DGEntry) (DGKey -> Maybe Vertex)

-------------------------------------------------------------------------------
-- Dependency analysis                                                       --
-------------------------------------------------------------------------------

-- | A strongly connected component of the dependency graph.
--
--   All declarations that mutually depend on each other are in the same
--   strongly connected component.
--
--   The only difference to @'SCC' 'HS.Decl'@ is that the constructors
--   have been renamed to be more explainatory in the context of dependency
--   analysis.
data DependencyComponent =
  NonRecursive (HS.Decl) -- ^ A single non-recursive declaration.
  | Recursive [HS.Decl]  -- ^ A list of mutually recursive declarations.

-- | Converts a strongly connected component from @Data.Graph@ to a
--   'DependencyComponent'.
convertSCC :: SCC HS.Decl -> DependencyComponent
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
groupDependencies :: DependencyGraph -> [DependencyComponent]
groupDependencies (DependencyGraph graph getEntry _) =
  map convertSCC $ stronglyConnComp $ map getEntry $ vertices graph

-- | Combines the construction of the dependency graphs for the given
--   declarations (See 'typeDependencyGraph' and 'funcDependencyGraph') with
--   the computaton of strongly connected components.
groupDeclarations :: [HS.Decl] -> [DependencyComponent]
groupDeclarations decls = concatMap
  groupDependencies
  [typeDependencyGraph decls, funcDependencyGraph decls]

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
typeDeclEntries decl@(HS.TypeDecl ident typeArgs typeExpr) = Just
  (decl, HS.Ident ident, Set.toList ds)
  where ds = withoutArgs typeArgs (typeDependencies typeExpr)
typeDeclEntries decl@(HS.DataDecl ident typeArgs conDecls) = Just
  (decl, HS.Ident ident, Set.toList ds)
  where ds = withoutArgs typeArgs (Set.unions (map conDeclDependencies conDecls))
typeDeclEntries _ = Nothing

-- | Gets the keys of the type constructors used by the fields of the given
--   constructor.
conDeclDependencies :: HS.ConDecl -> Set DGKey
conDeclDependencies (HS.ConDecl _ types) = Set.unions (map typeDependencies types)

-- | Gets the keys for the type constructors used by the given type expression.
typeDependencies :: HS.Type -> Set DGKey
typeDependencies (HS.TypeVar ident) = Set.singleton (HS.Ident ident)
typeDependencies (HS.TypeCon name ) = Set.singleton name
typeDependencies (HS.TypeApp t1 t2) =
  typeDependencies t1 `Set.union` typeDependencies t2
typeDependencies (HS.TypeFunc t1 t2) =
  typeDependencies t1 `Set.union` typeDependencies t2

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
funcDeclEntries decl@(HS.FuncDecl ident args expr) = Just
  (decl, HS.Ident ident, Set.toList ds)
  where ds = withoutArgs args (exprDependencies expr)
funcDeclEntries _ = Nothing

-- | Gets the keys for the functions used by the given expression.
--
--   This does not include the keys for local variables (i.e. arguments or
--   patterns).
exprDependencies :: HS.Expr -> Set DGKey
exprDependencies (HS.Con name) = Set.singleton name
exprDependencies (HS.Var name) = Set.singleton name
exprDependencies (HS.App e1 e2) =
  exprDependencies e1 `Set.union` exprDependencies e2
exprDependencies (HS.InfixApp e1 op e2) =
  Set.unions (opDependencies op : map exprDependencies [e1, e2])
exprDependencies (HS.LeftSection e1 op) =
  opDependencies op `Set.union` exprDependencies e1
exprDependencies (HS.RightSection op e2) =
  opDependencies op `Set.union` exprDependencies e2
exprDependencies (HS.NegApp expr) = exprDependencies expr
exprDependencies (HS.If e1 e2 e3) =
  Set.unions (map exprDependencies [e1, e2, e3])
exprDependencies (HS.Case expr alts) =
  Set.unions (exprDependencies expr : map altDependencies alts)
exprDependencies (HS.Undefined   ) = Set.empty
exprDependencies (HS.ErrorExpr  _) = Set.empty
exprDependencies (HS.IntLiteral _) = Set.empty
exprDependencies (HS.Lambda args expr) =
  withoutArgs args (exprDependencies expr)

-- | Gets the keys for the functions and constructors used by the given case
--   expression alternative.
altDependencies :: HS.Alt -> Set DGKey
altDependencies (HS.Alt conName args expr) =
  Set.insert conName (withoutArgs args (exprDependencies expr))

-- | Gets the key for a function or constructor used in infix notation.
opDependencies :: HS.Op -> Set DGKey
opDependencies (HS.VarOp name) = Set.singleton name
opDependencies (HS.ConOp name) = Set.singleton name

withoutArgs :: [String] -> Set DGKey -> Set DGKey
withoutArgs args set = set \\ Set.fromList (map HS.Ident args)

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
