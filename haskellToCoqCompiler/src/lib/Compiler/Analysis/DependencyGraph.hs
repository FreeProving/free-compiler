-- | This module contains functions to construct dependency graphs of
--   Haskell modules. A dependency graph is a directed graph whose nodes
--   are labelled with declarations. There is an edge from node @A@ to @B@
--   if the declaration of @A@ depends on the declaration of @B@ (i.e. in Coq
--   @B@ has to be defined before @A@ or both have to be declared in the same
--   sentence).

--   The dependency graph does only contain global, user defined declarations
--   (i.e. there are no nodes for build in data types or operations and there
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
  , DependencyGraph
  , errorKey
  , undefinedKey
  , entries
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

import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.Pretty
import           Compiler.Util.Data.Tuple

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
typeDeclEntries decl@(HS.TypeDecl _ (HS.DeclIdent _ ident) typeArgs typeExpr) =
  Just (decl, HS.Ident ident, Set.toList ds)
 where
  ds :: Set DGKey
  ds = withoutTypeArgs typeArgs (typeDependencies typeExpr)
typeDeclEntries decl@(HS.DataDecl _ (HS.DeclIdent _ ident) typeArgs conDecls) =
  Just (decl, HS.Ident ident, Set.toList ds)
 where
  ds :: Set DGKey
  ds = withoutTypeArgs typeArgs (Set.unions (map conDeclDependencies conDecls))
typeDeclEntries _ = Nothing

-- | Gets the keys of the type constructors used by the fields of the given
--   constructor.
conDeclDependencies :: HS.ConDecl -> Set DGKey
conDeclDependencies (HS.ConDecl _ _ types) =
  Set.unions (map typeDependencies types)

-- | Gets the keys for the type constructors used by the given type expression.
typeDependencies :: HS.Type -> Set DGKey
typeDependencies (HS.TypeVar _ ident) = Set.singleton (HS.Ident ident)
typeDependencies (HS.TypeCon _ name ) = Set.singleton name
typeDependencies (HS.TypeApp _ t1 t2) =
  typeDependencies t1 `Set.union` typeDependencies t2
typeDependencies (HS.TypeFunc _ t1 t2) =
  typeDependencies t1 `Set.union` typeDependencies t2

-- | Removes the keys for the given type variable declarations from a set of
--   dependencies.
withoutTypeArgs :: [HS.TypeVarDecl] -> Set DGKey -> Set DGKey
withoutTypeArgs args set = set \\ Set.fromList (map varPatToName args)
 where
  varPatToName :: HS.TypeVarDecl -> HS.Name
  varPatToName (HS.DeclIdent _ ident) = HS.Ident ident

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
funcDeclEntries decl@(HS.FuncDecl _ (HS.DeclIdent _ ident) args expr) = Just
  (decl, HS.Ident ident, Set.toList ds)
 where
  ds :: Set DGKey
  ds = withoutArgs args (exprDependencies expr)
funcDeclEntries _ = Nothing

-- | Gets the keys for the functions and constructors used by the given
--   expression.
--
--   This does not include the keys for local variables (i.e. arguments or
--   patterns). The keys of the special functions `undefined` and `error` are
--   included, because they are neccessary to identify partial functions.
exprDependencies :: HS.Expr -> Set DGKey
exprDependencies (HS.Con _ name) = Set.singleton name
exprDependencies (HS.Var _ name) = Set.singleton name
exprDependencies (HS.App _ e1 e2) =
  exprDependencies e1 `Set.union` exprDependencies e2
exprDependencies (HS.InfixApp _ e1 op e2) =
  Set.unions (opDependencies op : map exprDependencies [e1, e2])
exprDependencies (HS.LeftSection _ e1 op) =
  opDependencies op `Set.union` exprDependencies e1
exprDependencies (HS.RightSection _ op e2) =
  opDependencies op `Set.union` exprDependencies e2
exprDependencies (HS.NegApp _ expr) = exprDependencies expr
exprDependencies (HS.If _ e1 e2 e3) =
  Set.unions (map exprDependencies [e1, e2, e3])
exprDependencies (HS.Case _ expr alts) =
  Set.unions (exprDependencies expr : map altDependencies alts)
exprDependencies (HS.Undefined _   ) = Set.singleton (HS.Ident "undefined")
exprDependencies (HS.ErrorExpr  _ _) = Set.singleton (HS.Ident "error")
exprDependencies (HS.IntLiteral _ _) = Set.empty
exprDependencies (HS.Lambda _ args expr) =
  withoutArgs args (exprDependencies expr)

-- | Gets the keys for the functions and constructors used by the given case
--   expression alternative.
altDependencies :: HS.Alt -> Set DGKey
altDependencies (HS.Alt _ (HS.ConPat _ conName) args expr) =
  Set.insert conName (withoutArgs args (exprDependencies expr))

-- | Gets the key for a function or constructor used in infix notation.
opDependencies :: HS.Op -> Set DGKey
opDependencies (HS.VarOp _ name) = Set.singleton name
opDependencies (HS.ConOp _ name) = Set.singleton name

-- | Removes the keys for the given variable patterns from a set of
--   dependencies.
withoutArgs :: [HS.VarPat] -> Set DGKey -> Set DGKey
withoutArgs args set = set \\ Set.fromList (map varPatToName args)
 where
  varPatToName :: HS.VarPat -> HS.Name
  varPatToName (HS.VarPat _ ident) = HS.Ident ident

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
