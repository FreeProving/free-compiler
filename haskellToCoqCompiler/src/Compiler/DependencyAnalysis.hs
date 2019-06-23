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
--   reason the function dependency graph does not include constructors.
--
--   The dependency analysis does not yet test whether there are undefined
--   identifiers.
--
--   For debugging purposes dependency graphs can be converted to the DOT
--   format such that they can be visualized using Graphviz
--   (See <https://www.graphviz.org/>).

module Compiler.DependencyAnalysis
  ( DGKey
  , DGNode
  , DGEntry
  , DependencyGraph
  , typeDependencyGraph
  , funcDependencyGraph
  , prettyGraph
  )
where

import           Data.Graph
import           Data.Maybe                     ( catMaybes
                                                , maybeToList
                                                )
import           Data.List                      ( nub )
import qualified Data.Text.Lazy                as TL

import qualified Language.Haskell.Exts.Syntax  as H
import           Text.PrettyPrint.Leijen.Text

-- | Every node of the dependency graph is uniquely identified by a key.
--   We use the Haskell identifiers to identify the nodes.
type DGKey = String

-- | The nodes of the dependency graph are Haskell declaraions.
type DGNode l = H.Decl l

-- | Every node (declaration) in a dependency graph is associated with a
--   unique key (Haskell identifier) and a list of keys that identify the
--   nodes this node depends on (adjacency list).
type DGEntry l = (DGNode l, DGKey, [DGKey])

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
type DependencyGraph l = (Graph, Vertex -> DGEntry l, DGKey -> Maybe Vertex)

-------------------------------------------------------------------------------
-- Type dependencies                                                         --
-------------------------------------------------------------------------------

-- | Creates the dependency graph for a list of data type or type synonym
--   declarations.
typeDependencyGraph :: [H.Decl l] -> DependencyGraph l
typeDependencyGraph = graphFromEdges . map typeDeclEntries . filter isTypeDecl

-- | Tests whether the given declaration is a data type or type synonym
--   declaration.
isTypeDecl :: H.Decl l -> Bool
isTypeDecl (H.TypeDecl _ _ _      ) = True
isTypeDecl (H.DataDecl _ _ _ _ _ _) = True
isTypeDecl _                        = False

-- | Creates an entry of the dependency graph for the given data type or type
--   synonym declaration.
typeDeclEntries :: H.Decl l -> DGEntry l
typeDeclEntries decl@(H.TypeDecl _ declHead typeExpr) =
  (decl, keyFromDeclHead declHead, nub $ typeDependencies typeExpr)
typeDeclEntries decl@(H.DataDecl _ _ _ declHead cs _) =
  (decl, keyFromDeclHead declHead, nub $ concatMap qualConDeclDependencies cs)

-- | Gets the keys of the type constructors used by the fields of the given
--   constructor.
qualConDeclDependencies :: H.QualConDecl l -> [DGKey]
qualConDeclDependencies (H.QualConDecl _ _ _ (H.ConDecl _ _ types)) =
  concatMap typeDependencies types

-- | Gets the key for a type declaration from the head of the declaration.
keyFromDeclHead :: H.DeclHead l -> DGKey
keyFromDeclHead (H.DHead   _ name    ) = nameToKey name
keyFromDeclHead (H.DHParen _ declHead) = keyFromDeclHead declHead
keyFromDeclHead (H.DHApp _ declHead _) = keyFromDeclHead declHead

-- | Gets the keys for the type constructors used by the given type expression.
typeDependencies :: H.Type l -> [DGKey]
typeDependencies (H.TyFun _ t1 t2) = typeDependencies t1 ++ typeDependencies t2
typeDependencies (H.TyTuple _ _  ts) = concatMap typeDependencies ts
typeDependencies (H.TyList _ t     ) = typeDependencies t
typeDependencies (H.TyApp _ t1 t2) = typeDependencies t1 ++ typeDependencies t2
typeDependencies (H.TyVar   _ _    ) = []
typeDependencies (H.TyCon   _ qName) = maybeToList (qNameToKey qName)
typeDependencies (H.TyParen _ t    ) = typeDependencies t

-------------------------------------------------------------------------------
-- Function dependencies                                                     --
-------------------------------------------------------------------------------

-- | Creates the dependency graph for a list of function declarations or
--   pattern bindings.
funcDependencyGraph :: [H.Decl l] -> DependencyGraph l
funcDependencyGraph = graphFromEdges . map funcDeclEntries . filter isFuncDecl

-- | Tests whether the give declaration is a function declaration or pattern
--   binding.
isFuncDecl :: H.Decl l -> Bool
isFuncDecl (H.FunBind _ _    ) = True
isFuncDecl (H.PatBind _ _ _ _) = True
isFuncDecl _                   = False

-- | Creates an entry of the dependency graph for the given function
--   declaration or pattern binding.
funcDeclEntries :: H.Decl l -> DGEntry l
funcDeclEntries decl@(H.FunBind _ [H.Match _ name args (H.UnGuardedRhs _ expr) _])
  = (decl, nameToKey name, nub $ withoutArgs args $ exprDependencies expr)
funcDeclEntries decl@(H.PatBind _ (H.PVar _ name) (H.UnGuardedRhs _ expr) _) =
  (decl, nameToKey name, nub $ exprDependencies expr)

-- | Gets the keys for the functions or pattern bindings used by the
--   given expression.
--
--   This does not include the keys for constructors or local variables
--   (i.e. arguments or patterns).
exprDependencies :: H.Exp l -> [DGKey]
exprDependencies (H.Var _ qName) = maybeToList (qNameToKey qName)
exprDependencies (H.Con _ _    ) = []
exprDependencies (H.Lit _ _    ) = []
exprDependencies (H.InfixApp _ e1 qOp e2) =
  qOpDependencies qOp ++ concatMap exprDependencies [e1, e2]
exprDependencies (H.App _ e1 e2  ) = concatMap exprDependencies [e1, e2]
exprDependencies (H.NegApp _ expr) = exprDependencies expr
exprDependencies (H.Lambda _ args expr) =
  withoutArgs args $ exprDependencies expr
exprDependencies (H.If _ e1 e2 e3) = concatMap exprDependencies [e1, e2, e3]
exprDependencies (H.Case _ expr alts) =
  exprDependencies expr ++ concatMap altDependencies alts
exprDependencies (H.Tuple _ _ exprs) = concatMap exprDependencies exprs
exprDependencies (H.List  _ exprs  ) = concatMap exprDependencies exprs
exprDependencies (H.Paren _ expr   ) = exprDependencies expr
exprDependencies (H.LeftSection _ expr qOp) =
  qOpDependencies qOp ++ exprDependencies expr
exprDependencies (H.RightSection _ qOp expr) =
  qOpDependencies qOp ++ exprDependencies expr

-- | Gets the keys for the functions or pattern bindings used on the right hand
--   side of the given case expression alternative.
altDependencies :: H.Alt l -> [DGKey]
altDependencies (H.Alt _ pat (H.UnGuardedRhs _ expr) _) =
  withoutArgs [pat] $ exprDependencies expr

-- | Gets the key for a function used in infix notation.
--
--   This does not include the keys for constructors because data type
--   declarations are supposed to occur before function declarations.
qOpDependencies :: H.QOp l -> [DGKey]
qOpDependencies (H.QVarOp _ qName) = maybeToList (qNameToKey qName)
qOpDependencies (H.QConOp _ _    ) = []

-- | Removes the keys for variable patterns in the first list from the given
--   list of keys.
--
--   This function is used to filter local variables in 'exprDependencies'.
withoutArgs :: [H.Pat l] -> [DGKey] -> [DGKey]
withoutArgs patterns keys = deleteAll (concatMap pVarKeys patterns) keys

-- | Gets the keys for all variable patterns in the given pattern.
pVarKeys :: H.Pat l -> [DGKey]
pVarKeys (H.PVar _ name        ) = [nameToKey name]
pVarKeys (H.PInfixApp _ p1 _ p2) = concatMap pVarKeys [p1, p2]
pVarKeys (H.PApp   _ _ ps      ) = concatMap pVarKeys ps
pVarKeys (H.PTuple _ _ ps      ) = concatMap pVarKeys ps
pVarKeys (H.PList  _ ps        ) = concatMap pVarKeys ps
pVarKeys (H.PParen _ pat       ) = pVarKeys pat

-------------------------------------------------------------------------------
-- Convert Haskell names to keys                                             --
-------------------------------------------------------------------------------

-- | Converts a Haskell identifier or symbol to a key for a node in the
--   dependency graph. Returns 'Nothing' if the given name identifies
--   a special constructor (e.g. list or pair constructor).
--
--   Qualified identifiers are not supported at the moment.
qNameToKey :: H.QName l -> Maybe DGKey
qNameToKey (H.UnQual  _ name) = Just (nameToKey name)
qNameToKey (H.Special _ _   ) = Nothing

-- | Converts a Haskell identifier or symbol to a key for a node in the
--   dependency graph.
nameToKey :: H.Name l -> DGKey
nameToKey (H.Ident  _ ident) = ident
nameToKey (H.Symbol _ sym  ) = "(" ++ sym ++ ")"

-------------------------------------------------------------------------------
-- Utility functions                                                         --
-- TODO create module for utility functions                                  --
-------------------------------------------------------------------------------

-- | Removes all occurrences of all elements in the first list from the second
--   list.
deleteAll
  :: Eq a
  => [a] -- The list of items to remove.
  -> [a] -- The list to remove items from.
  -> [a]
deleteAll xs ys = [ y | y <- ys, not (y `elem` xs) ]

-------------------------------------------------------------------------------
-- Pretty print dependency graph                                             --
-------------------------------------------------------------------------------

-- | Pretty prints the dependency graph in DOT format.
prettyGraph :: DependencyGraph l -> Doc
prettyGraph (graph, getEntry, getVertex) =
  digraph
    <+> braces (line <> indent 2 (vcat (nodeDocs ++ edgesDocs)) <> line)
    <>  line
 where
  -- | A document for the DOT digraph keyword.
  digraph :: Doc
  digraph = text (TL.pack "digraph")

  -- | A document for the DOT label attribute.
  label :: Doc
  label = text (TL.pack "label")

  -- | A document for the DOT arrow symbol.
  arrow :: Doc
  arrow = text (TL.pack "->")

  -- | Pretty printed DOT nodes for the dependency graph.
  nodeDocs :: [Doc]
  nodeDocs = map prettyNode (vertices graph)

  -- | Pretty prints the given vertex as a DOT command. The key of the node
  --   is used a the label.
  prettyNode :: Vertex -> Doc
  prettyNode v =
    let (_, key, _) = getEntry v
    in  int v
        <+> brackets (label <> equals <> dquotes (text (TL.pack key)))
        <>  semi

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
