-- | This module contains functions and data structures for analyzing the data
--   flow among mutually recursive IR functions. The goal is to find arguments
--   that are never changed throughout the computation. One example for such
--   a "constant argument" is the function passed to @map@.
--
--   @
--   map f xs = case xs of { [] -> []; (:) x xs' -> (:) (f x) (map f xs') }
--   @
--
--   The argument @f@ is passed unchanged to @map@ in every recursive call.
--
--   Functions with such recursive calls can be declared inside a @Section@
--   sentence in Coq where the declaration of @f@ is moved outside the
--   declaration of @map@
--   (see also "FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithSections").
--
--   @
--   Section map_section.
  --    ⋮
  --   Variable f : (* … *).
  --    ⋮
  --   Definition map (xs : …) := (* … *).
--   End map_section.
--   @
--
--   Within the section, @map@ has only one argument @xs@ but can use @f@
--   normally. Outside the section it appears as if @map@ has an additional
--   argument @f@. The section aids Coq's to recognize whether recursive
--   functions that use @map@ and have recursive calls in @f@ terminate.
--   See @doc/CustomPragmas/DecreasingArgumentPragma.md@ for details and
--   examples.
module FreeC.Backend.Coq.Analysis.ConstantArguments
  ( ConstArg(..)
  , identifyConstArgs
  )
where

-------------------------------------------------------------------------------
-- Constant Arguments                                                        --
-------------------------------------------------------------------------------

-- | Data type that represents a constant argument shared by multiple
--   mutually recursive functions.
--
--   Contains the names and indicies of the corrsponding arguments of the
--   function declarations and a fresh identifier for the @Variable@ sentence
--   that replaces the constant argument.
data ConstArg = ConstArg
  { constArgIdents     :: Map HS.QName String
    -- ^ Maps the names of functions that share the constant argument to the
    --   names of the corresponding function arguments.
  , constArgIndicies   :: Map HS.QName Int
    -- ^ Maps the names of functions that share the constant argument to the
    --   index of the corresponding function argument.
  , constArgFreshIdent :: String
    -- ^ A fresh identifier for the constant argument.
  }
 deriving Show

-------------------------------------------------------------------------------
-- Constant Argument Graph                                                   --
-------------------------------------------------------------------------------

-- | Nodes of the the constant argument graph (see 'makeConstArgGraph') are
--   pairs of function and argument names.
type CGNode = (HS.QName, String)

-- | The nodes of the the constant argument graph (see 'makeConstArgGraph')
--   are identified by themselves.
type CGEntry = (CGNode, CGNode, [CGNode])

-- | Constructs a graph that is used to identify contant arguments, i.e.,
--   arguments that are passed unchanged between the given function
--   declarations.
--
--   The graph is constructed as follows:
--
--    * Create one node @(f, x_i)@ for each function declarations
--      @f x_0 ... x_n = e@ and argument @x_i ∊ {x_0, ..., x_n}@.
--    * For each pair of function declarations @f x_0 ... x_n = e@
--      and @g y_0 ... y_m = e'@ draw an edge from @(f,x_i)@ and
--      @(g,y_j)@ if and only if every application @g e_0 ... e_m@
--      in @e@ has the form @g e_0 ... e_{j-1} x_i e_{j+1} ... e_m@
--      (i.e., the argument @x_i@ is passed unchanged to the @j@-th
--      argument @g@).
makeConstArgGraph :: [HS.FuncDecl] -> [CGEntry]
makeConstArgGraph decls = do
  -- Create one node @(f,x_i)@ for every argument @x_i@ of every function @f@.
  (node@(_f, x), _i, rhs) <- nodes
  -- Generate outgoing edges of @(f,x_i)@.
  let
    adjacent = do
      -- Consider every node @(g,y_j)@.
      ((g, y), j, _) <- nodes
      -- Test whether there is any call to @g@ on the right-hand side of @f@.
      let callsG :: HS.Expr -> Bool
          callsG = elem g . freeVarSet
      guard (callsG rhs)
      -- Test whether @x_i@ is passed unchanged to @y_j@ in every call
      -- to @g@ in the right-hand side of @f@.
      let
        -- | Tests whether the given expression (a value passed as the @j@-th
        --   argument to a call to @g@) is the argument @x_i@.
        checkArg :: HS.Expr -> Bool
        checkArg (HS.Var _ (HS.UnQual (HS.Ident ident)) _) = ident == x
        checkArg _ = False

        -- | Tests whether @x_j@ is passed unchanged as the @j@-th argument
        --   to every call to @g@ in the given expression.
        --
        --   The second argument contains the arguments that are passed to
        --   the current expression.
        checkExpr :: HS.Expr -> [HS.Expr] -> Bool

        -- If this is a call to @g@, check the @j@-th argument.
        checkExpr (HS.Var _ name _) args
          | name == g = j < length args && checkArg (args !! j)
          | otherwise = True

        -- If this is an application, check for calls to @g@ in the callee
        -- and argument.
        checkExpr (HS.App _ e1 e2 _) args =
          checkExpr e1 (e2 : args) && checkExpr e2 []

        -- The arguments are not distributed among the branches of @if@
        -- and @case@ expressions.
        checkExpr (HS.If _ e1 e2 e3 _) _ =
          checkExpr e1 [] && checkExpr e2 [] && checkExpr e3 []
        checkExpr (HS.Case _ expr alts _) _ =
          checkExpr expr [] && all (flip checkAlt []) alts

        -- No beta reduction is applied when a lambda expression is
        -- encountered, but the right-hand side still needs to be checked.
        -- If an argument shadows @x_i@ and there are calls to @g@ on the
        -- right hand side, @x_i@ is not left unchanged.
        checkExpr (HS.Lambda _ args expr _) _
          | x `shadowedBy` args = not (callsG expr)
          | otherwise           = checkExpr expr []

        -- Check visibly applied expression recursively.
        checkExpr (HS.TypeAppExpr _ expr _ _) args = checkExpr expr args

        -- Constructors, literals and error terms cannot contain further
        -- calls to @g@.
        checkExpr (HS.Con        _ _ _      ) _    = True
        checkExpr (HS.IntLiteral _ _ _      ) _    = True
        checkExpr (HS.Undefined _ _         ) _    = True
        checkExpr (HS.ErrorExpr _ _ _       ) _    = True

        -- | Applies 'checkExpr' to the alternative of a @case@ expression.
        --
        --   If a variable pattern shadows @x_i@, @x_i@ is not unchanged.
        checkAlt :: HS.Alt -> [HS.Expr] -> Bool
        checkAlt (HS.Alt _ _ varPats expr) args
          | x `shadowedBy` varPats = not (callsG expr)
          | otherwise              = checkExpr expr args

        -- | Tests whethe the given variable is shadowed by the given
        --   variale patterns.
        shadowedBy :: String -> [HS.VarPat] -> Bool
        shadowedBy = flip (flip elem . map HS.varPatIdent)
      guard (checkExpr rhs [])
      -- Add edge if the test was successful.
      return (g, y)
  return (node, node, adjacent)
 where
  -- | There is one node for each argument of every function declaration.
  nodes :: [(CGNode, Int, HS.Expr)]
  nodes = do
    decl <- decls
    let funcName = HS.funcDeclQName decl
        args     = HS.funcDeclArgs decl
        rhs      = HS.funcDeclRhs decl
    (argName, argIndex) <- zip (map HS.varPatIdent args) [0 ..]
    return ((funcName, argName), argIndex, rhs)

-------------------------------------------------------------------------------
-- Identifying Constant Arguments                                            --
-------------------------------------------------------------------------------

-- | Identifies function arguments that can be moved to a @Section@
--   sentence in Coq.
--
--   The call graph of the given function declarations should be strongly
--   connected.
identifyConstArgs :: [HS.FuncDecl] -> Converter [ConstArg]
identifyConstArgs decls = mapM makeConstArg constArgNameMaps
 where
  -- | Maps for each set of constant arguments the names of the functions to
  --   the name the constant argument has in that function.
  constArgNameMaps :: [Map HS.QName String]
  constArgNameMaps = identifyConstArgs' decls

  -- Creates 'ConstArg's from the 'constArgNameMaps'.
  makeConstArg :: Map HS.QName String -> Converter ConstArg
  makeConstArg identMap = do
    let idents = nub (Map.elems identMap)
        prefix = intercalate "_" idents
    freshIdent <- freshHaskellIdent prefix
    return ConstArg { constArgIdents = identMap
                    , constArgIndicies = Map.mapWithKey lookupArgIndex identMap
                    , constArgFreshIdent = freshIdent
                    }

  -- | Maps the names of the function declarations to the names of their
  --   arguments.
  argNamesMap :: Map HS.QName [String]
  argNamesMap = Map.fromList
    [ (HS.funcDeclQName decl, map HS.varPatIdent (HS.funcDeclArgs decl))
    | decl <- decls
    ]

  -- | Looks up the index of the argument with the given name of the function
  --   with the given name.
  lookupArgIndex
    :: HS.QName -- ^ The name of the function.
    -> String   -- ^ The name of the argument.
    -> Int
  lookupArgIndex funcName argName = fromJust $ do
    argNames <- Map.lookup funcName argNamesMap
    elemIndex argName argNames

-- | Like 'identifyConstArgs' but returns a map from function to argument names
--   for each constant argument instead of a 'ConstArg'.
identifyConstArgs' :: [HS.FuncDecl] -> [Map HS.QName String]
identifyConstArgs' decls =
  map Map.fromList $ filter checkSCC $ mapMaybe fromCyclicSCC $ stronglyConnComp
    constArgGraph
 where
  -- | The constant argument graph.
  constArgGraph :: [CGEntry]
  constArgGraph = makeConstArgGraph decls

  -- | Maps the keys of the 'constArgGraph' to the adjacency lists.
  constArgMap :: Map CGNode [CGNode]
  constArgMap = Map.fromList [ (k, ks) | (_, k, ks) <- constArgGraph ]

  -- | The dependency graph of the function declarations.
  callGraph :: DependencyGraph HS.FuncDecl
  callGraph = funcDependencyGraph decls

  -- | Tests whether the given strongly connected component describes a
  --   valid set of constant arguments.
  --
  --   The strongly connected component must contain every function
  --   exactly once (see 'containsAllFunctions') and if there is an edge
  --   between two functions in the 'callGraph', there must also be an
  --   edge between the corresponding nodes of the 'constArgGraph'.
  checkSCC :: [CGNode] -> Bool
  checkSCC nodes
    | not (containsAllFunctions nodes) = False
    | otherwise = and $ do
      (f, x) <- nodes
      (g, y) <- nodes
      -- If there is an edge from @f@ to @g@ in the call graph, ...
      guard (dependsDirectlyOn callGraph f g)
      -- ... there must also be an edge in the constant argument graph.
      adjacent <- maybeToList (Map.lookup (f, x) constArgMap)
      return ((g, y) `elem` adjacent)

  -- | The names of all given function declarations.
  funcNames :: [HS.QName]
  funcNames = map HS.funcDeclQName decls

  -- | Tests whether the given list of nodes contains one node for every
  --   function declaration.
  containsAllFunctions :: [CGNode] -> Bool
  containsAllFunctions nodes =
    length nodes == length decls && all (`elem` map fst nodes) funcNames

  -- | Gets the nodes of a cyclic strongly connected component.
  fromCyclicSCC :: SCC CGNode -> Maybe [CGNode]
  fromCyclicSCC (AcyclicSCC _    ) = Nothing
  fromCyclicSCC (CyclicSCC  nodes) = Just nodes
