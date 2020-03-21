-- | This module contains functions for analysising recursive function, e.g. to
--   finding the decreasing argument of a recursive function and to find
--   constant arguments of recursive functions.

module Compiler.Analysis.RecursionAnalysis
  ( -- * Decreasing arguments
    DecArgIndex
  , identifyDecArgs
    -- * Constant arguments
  , ConstArg(..)
  , identifyConstArgs
  )
where

import           Control.Monad                  ( guard )
import           Data.Graph
import           Data.List                      ( elemIndex
                                                , find
                                                , intercalate
                                                , nub
                                                )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( catMaybes
                                                , fromJust
                                                , maybeToList
                                                )
import           Data.Set                       ( Set
                                                , (\\)
                                                )
import qualified Data.Set                      as Set
import           Data.Tuple.Extra               ( uncurry3 )

import           Compiler.Analysis.DependencyExtraction
                                                ( varSet )
import           Compiler.Analysis.DependencyGraph
import           Compiler.Environment
import           Compiler.Environment.Fresh
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty
import           Compiler.Util.Predicate        ( (.||.) )

-------------------------------------------------------------------------------
-- Decreaasing arguments                                                     --
-------------------------------------------------------------------------------

-- | Type for the index of a decreasing argument.
type DecArgIndex = Int

-- | Guesses all possible combinations of decreasing arguments for the given
--   mutually recursive function declarations.
--
--   The second argument contains the known decreasing arguments as specified
--   by the user.
--
--   Returns a list of all possible combinations of argument indecies.
guessDecArgs :: [HS.FuncDecl] -> [Maybe DecArgIndex] -> [[DecArgIndex]]
guessDecArgs []          _  = return []
guessDecArgs _           [] = return []
guessDecArgs (_ : decls) (Just decArgIndex : knownDecArgIndecies) = do
  decArgIndecies <- guessDecArgs decls knownDecArgIndecies
  return (decArgIndex : decArgIndecies)
guessDecArgs (decl : decls) (Nothing : knownDecArgIndecies) = do
  let arity = length (HS.funcDeclArgs decl)
  decArgIndecies <- guessDecArgs decls knownDecArgIndecies
  decArgIndex    <- [0 .. arity - 1]
  return (decArgIndex : decArgIndecies)

-- | Tests whether the given combination of choices for the decreasing
--   arguments of function declarations in a strongly connected component
--   is valid (i.e. all function declarations actually decrease the
--   corresponding argument).
--
--   The second argument contains the known decreasing arguments as specified
--   by the user. If the user has specied the decreasing argument of a function
--   it is not checked whether the function actually decreases on the argument
--   (such that the user is not limited by our termination checker).
checkDecArgs :: [HS.FuncDecl] -> [Maybe DecArgIndex] -> [DecArgIndex] -> Bool
checkDecArgs decls knownDecArgIndecies decArgIndecies = all
  (uncurry3 checkDecArg)
  (zip3 knownDecArgIndecies decArgIndecies decls)
 where
  -- | Maps the names of functions in the strongly connected component
  --   to the index of their decreasing argument.
  decArgMap :: Map HS.QName DecArgIndex
  decArgMap =
    foldr (uncurry insertFuncDecl) Map.empty (zip decls decArgIndecies)

  -- | Inserts a function declaration with the given decreasing argument index
  --   into 'decArgMap'.
  insertFuncDecl
    :: HS.FuncDecl
    -> DecArgIndex
    -> Map HS.QName DecArgIndex
    -> Map HS.QName DecArgIndex
  insertFuncDecl = Map.insert . HS.funcDeclQName

  -- | Tests whether the given function declaration actually decreases on the
  --   argument with the given index.
  --
  --   The first argument is the index of the decreasing argument as specified
  --   by the user or @Nothing@ if there is no such annotation.
  checkDecArg :: Maybe DecArgIndex -> DecArgIndex -> HS.FuncDecl -> Bool
  checkDecArg (Just _) _ _ = True
  checkDecArg _ decArgIndex (HS.FuncDecl _ _ _ args expr _) =
    let decArg = HS.varPatQName (args !! decArgIndex)
    in  checkExpr decArg Set.empty expr []

  -- | Tests whether there is a variable that is structurally smaller than the
  --   argument with the given name in the position of decreasing arguments of
  --   all applications of functions from the strongly connected component.
  --
  --   The second argument is a set of variables that are known to be
  --   structurally smaller than the decreasing argument of the function
  --   whose right hand side is checked.
  --
  --   The last argument is a list of actual arguments passed to the given
  --   expression.
  checkExpr :: HS.QName -> Set HS.QName -> HS.Expr -> [HS.Expr] -> Bool
  checkExpr decArg smaller = checkExpr'
   where
    -- | Tests whether the given expression is the decreasing argument.
    isDecArg :: HS.Expr -> Bool
    isDecArg (HS.Var _ varName _) = varName == decArg
    isDecArg _                    = False

    -- | Tests whether the given expression is a structurally smaller
    --   variable than the decreasing argument.
    isSmaller :: HS.Expr -> Bool
    isSmaller (HS.Var _ varName _) = varName `elem` smaller
    isSmaller _                    = False

    -- | Tests whether the given expression matches 'isDecArg' or 'isSmaller'.
    isDecArgOrSmaller :: HS.Expr -> Bool
    isDecArgOrSmaller = isDecArg .||. isSmaller

    -- If one of the recursive functions is applied, there must be a
    -- structurally smaller variable in the decreasing position.
    checkExpr' (HS.Var _ name _) args = case Map.lookup name decArgMap of
      Nothing -> True
      Just decArgIndex | decArgIndex >= length args -> False
                       | otherwise -> isSmaller (args !! decArgIndex)

    -- Function applications and @if@-expressions need to be checked
    -- recursively. In case of applications we also remember the
    -- arguments such that the case above can inspect the actual arguments.
    checkExpr' (HS.App _ e1 e2 _) args =
      checkExpr' e1 (e2 : args) && checkExpr' e2 []
    checkExpr' (HS.If _ e1 e2 e3 _) _ =
      checkExpr' e1 [] && checkExpr' e2 [] && checkExpr' e3 []

    -- @case@-expressions that match the decreasing argument or a variable
    -- that is structurally smaller than the decreasing argument, introduce
    -- new structurally smaller variables.
    checkExpr' (HS.Case _ expr alts _) _
      | isDecArgOrSmaller expr = all checkSmallerAlt alts
      | otherwise              = all checkAlt alts

    -- The arguments of lambda expressions shadow existing (structurally
    -- smaller) variables.
    checkExpr' (HS.Lambda _ args expr _) _ =
      let smaller' = withoutArgs args smaller
      in  checkExpr decArg smaller' expr []

    -- Recursively check visibly applied expressions.
    checkExpr' (HS.TypeAppExpr _ expr _ _) args = checkExpr' expr args

    -- Base expressions don't contain recursive calls.
    checkExpr' (HS.Con _ _ _             ) _    = True
    checkExpr' (HS.Undefined _ _         ) _    = True
    checkExpr' (HS.ErrorExpr  _ _ _      ) _    = True
    checkExpr' (HS.IntLiteral _ _ _      ) _    = True

    -- | Applies 'checkExpr' on the right hand side of an alternative of a
    --   @case@ expression.
    --
    --   The variable patterns shadow existing (structurally smaller) variables
    --   with the same name.
    checkAlt :: HS.Alt -> Bool
    checkAlt (HS.Alt _ _ varPats expr) =
      let smaller' = withoutArgs varPats smaller
      in  checkExpr decArg smaller' expr []

    -- | Like 'checkAlt' but for alternatives of @case@-expressions on
    --   the decreasing argument or a variable that is structurally smaller.
    --
    --   All variable patterns are added to the set of structurally smaller
    --   variables.
    checkSmallerAlt :: HS.Alt -> Bool
    checkSmallerAlt (HS.Alt _ _ varPats expr) =
      let smaller' = withArgs varPats smaller
      in  checkExpr decArg smaller' expr []

    -- | Adds the given variables to the set of structurally smaller variables.
    withArgs :: [HS.VarPat] -> Set HS.QName -> Set HS.QName
    withArgs args set = set `Set.union` Set.fromList (map HS.varPatQName args)

    -- | Removes the given variables to the set of structurally smaller
    --   variables (because they are shadowed by an argument from a lambda
    --   abstraction or @case@-alternative).
    withoutArgs :: [HS.VarPat] -> Set HS.QName -> Set HS.QName
    withoutArgs args set = set \\ Set.fromList (map HS.varPatQName args)

-- | Identifies the decreasing arguments of the given mutually recursive
--   function declarations.
--
--   The second argument contains the known decreasing arguments as specified
--   by the user.
--
--   Returns @Nothing@ if the decreasing argument could not be identified.
maybeIdentifyDecArgs
  :: [HS.FuncDecl] -> [Maybe DecArgIndex] -> Maybe [DecArgIndex]
maybeIdentifyDecArgs decls knownDecArgIndecies = find
  (checkDecArgs decls knownDecArgIndecies)
  (guessDecArgs decls knownDecArgIndecies)

-- | Identifies the decreasing arguments of the given mutually recursive
--   function declarations.
--
--   Reports a fatal error message, if the decreasing arguments could not be
--   identified.
identifyDecArgs :: [HS.FuncDecl] -> Converter [DecArgIndex]
identifyDecArgs decls = do
  knownDecArgIndecies <- mapM lookupDecArgIndexOfDecl decls
  maybe decArgError return (maybeIdentifyDecArgs decls knownDecArgIndecies)
 where
  -- | Looks up the index of an annotated decreasing argument.
  lookupDecArgIndexOfDecl :: HS.FuncDecl -> Converter (Maybe Int)
  lookupDecArgIndexOfDecl = inEnv . lookupDecArgIndex . HS.funcDeclQName

  -- | Prints an error message if the decreasing arguments could not
  --   be identified.
  decArgError :: Converter a
  decArgError =
    reportFatal
      $  Message (HS.funcDeclSrcSpan (head decls)) Error
      $  "Could not identify decreasing arguments of "
      ++ showPretty (map HS.funcDeclIdent decls)
      ++ ".\n"
      ++ "Consider adding a "
      ++ "{-# HASKELL_TO_COQ <function> DECREASES ON <argument> #-} "
      ++ "annotation."

-------------------------------------------------------------------------------
-- Constant arguments                                                        --
-------------------------------------------------------------------------------

-- | Data type that represents a constant argument shared by multiple
--   mutually recusive functions.
--
--   Contains the names and indicies of the corrsponding arguments of the
--   function declarations and a fresh identifier for the @Variable@ sentence
--   that replaces the constant argument.
data ConstArg = ConstArg
  { constArgIdents     :: Map String String
    -- ^ Maps the names of functions that share the constant argument to the
    --   names of the corresponding function arguments.
  , constArgIndicies   :: Map String Int
    -- ^ Maps the names of functions that share the constant argument to the
    --   index of the corresponding function argument.
  , constArgFreshIdent :: String
    -- ^ A fresh identifier for the constant argument.
  }
 deriving Show

-- | Nodes of the the constant argument graph (see 'makeConstArgGraph') are
--   pairs of function and argument names.
type CGNode = (String, String)

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
makeConstArgGraph :: HS.ModName -> [HS.FuncDecl] -> [CGEntry]
makeConstArgGraph modName decls = do
  -- Create one node @(f,x_i)@ for every argument @x_i@ of every function @f@.
  (node@(_f, x), _i, rhs) <- nodes
  -- Generate outgoing edges of @(f,x_i)@.
  let
    adjacent = do
      -- Consider every node @(g,y_j)@.
      ((g, y), j, _) <- nodes
      -- Test whether there is any call to @g@ on the right-hand side of @f@.
      -- @g@ could be called qualified or unqualified.
      let isG :: HS.QName -> Bool
          isG = (`elem` [HS.UnQual (HS.Ident g), HS.Qual modName (HS.Ident g)])

          callsG :: HS.Expr -> Bool
          callsG = any isG . varSet
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
          | isG name  = j < length args && checkArg (args !! j)
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
    HS.FuncDecl _ declIdent _ args rhs _ <- decls
    let funName = HS.fromDeclIdent declIdent
    (argName, argIndex) <- zip (map HS.varPatIdent args) [0 ..]
    return ((funName, argName), argIndex, rhs)

-- | Identifies function arguments that can be moved to a @Section@
--   sentence in Coq.
--
--   The call graph of the given function declarations should be strongly
--   connected.
identifyConstArgs :: [HS.FuncDecl] -> Converter [ConstArg]
identifyConstArgs decls = do
  modName <- inEnv envModName
  flip mapM (identifyConstArgs' modName decls) $ \identMap -> do
    let idents = nub (Map.elems identMap)
        prefix = intercalate "_" idents
    freshIdent <- freshHaskellIdent prefix
    return ConstArg { constArgIdents = identMap
                    , constArgIndicies = Map.mapWithKey lookupArgIndex identMap
                    , constArgFreshIdent = freshIdent
                    }
 where
  -- | Maps the names of the function declarations to the names of their
  --   arguments.
  argNamesMap :: Map String [String]
  argNamesMap =
    Map.fromList
      $ [ (HS.fromDeclIdent declIdent, map HS.varPatIdent args)
        | (HS.FuncDecl _ declIdent _ args _ _) <- decls
        ]

  -- | Looks up the index of the argument with the given name of the function
  --   with the given name.
  lookupArgIndex
    :: String -- ^ The name of the function.
    -> String -- ^ The name of the argument.
    -> Int
  lookupArgIndex funcName argName = fromJust $ do
    argNames <- Map.lookup funcName argNamesMap
    elemIndex argName argNames

-- | Like 'identifyConstArgs' but takes the name of the currently translated
--   module as an argument.
identifyConstArgs' :: HS.ModName -> [HS.FuncDecl] -> [Map String String]
identifyConstArgs' modName decls =
  map Map.fromList
    $ filter checkSCC
    $ catMaybes
    $ map fromCyclicSCC
    $ stronglyConnComp constArgGraph
 where
  -- | The constant argument graph.
  constArgGraph :: [CGEntry]
  constArgGraph = makeConstArgGraph modName decls

  -- | Maps the keys of the 'constArgGraph' to the adjacency lists.
  constArgMap :: Map CGNode [CGNode]
  constArgMap = Map.fromList [ (k, ks) | (_, k, ks) <- constArgGraph ]

  -- | The dependency graph of the function declarations.
  callGraph :: DependencyGraph HS.FuncDecl
  callGraph = funcDependencyGraph modName decls

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
      let f' = HS.UnQual (HS.Ident f)
          g' = HS.UnQual (HS.Ident g)
      -- If there is an edge from @f@ to @g@ in the call graph, ...
      guard (dependsDirectlyOn callGraph f' g')
      -- ... there must also be an edge in the constant argument graph.
      adjacent <- maybeToList (Map.lookup (f, x) constArgMap)
      return ((g, y) `elem` adjacent)

  -- | The names of all given function declarations.
  funcNames :: [String]
  funcNames = map (HS.fromDeclIdent . HS.funcDeclIdent) decls

  -- | Tests whether the given list of nodes contains one node for every
  --   function declaration.
  containsAllFunctions :: [CGNode] -> Bool
  containsAllFunctions nodes =
    length nodes == length decls && all (`elem` (map fst nodes)) funcNames

  -- | Gets the nodes of a cyclic strongly connected component.
  fromCyclicSCC :: SCC CGNode -> Maybe [CGNode]
  fromCyclicSCC (AcyclicSCC _    ) = Nothing
  fromCyclicSCC (CyclicSCC  nodes) = Just nodes
