-- | This module contains functions for analysising recursive function, e.g. to
--   finding the decreasing argument of a recursive function and to find
--   constant arguments of recursive functions.

module Compiler.Analysis.RecursionAnalysis
  ( -- * Decreasing arguments
    DecArgIndex
  , identifyDecArgs
    -- * Constant arguments
  , identifyConstArgs
  )
where

import           Control.Monad                  ( guard )
import           Data.Graph
import           Data.List                      ( find )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( catMaybes
                                                , maybeToList
                                                )
import           Data.Set                       ( Set
                                                , (\\)
                                                )
import qualified Data.Set                      as Set

import           Compiler.Analysis.DependencyGraph
import           Compiler.Analysis.DependencyExtraction
                                                ( varSet )
import           Compiler.Environment
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter

-------------------------------------------------------------------------------
-- Decreaasing arguments                                                     --
-------------------------------------------------------------------------------

-- | Type for the index of a decreasing argument.
type DecArgIndex = Int

-- | Guesses all possible combinations of decreasing arguments for the given
--   mutually recursive function declarations.
--
--   Returns a list of all possible combinations of argument indecies.
guessDecArgs :: [HS.FuncDecl] -> [[DecArgIndex]]
guessDecArgs []                               = return []
guessDecArgs (HS.FuncDecl _ _ args _ : decls) = do
  decArgIndecies <- guessDecArgs decls
  decArgIndex    <- [0 .. length args - 1]
  return (decArgIndex : decArgIndecies)

-- | Tests whether the given combination of choices for the decreasing
--   arguments of function declarations in a strongly connected component
--   is valid (i.e. all function declarations actually decrease the
--   corresponding argument)
checkDecArgs :: [HS.FuncDecl] -> [DecArgIndex] -> Bool
checkDecArgs decls decArgIndecies = all (uncurry checkDecArg)
                                        (zip decArgIndecies decls)
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
  insertFuncDecl (HS.FuncDecl _ (HS.DeclIdent _ ident) _ _) decArg =
    Map.insert (HS.UnQual (HS.Ident ident)) decArg

  -- | Tests whether the given function declaration actually decreases on the
  --   argument with the given index.
  checkDecArg :: DecArgIndex -> HS.FuncDecl -> Bool
  checkDecArg decArgIndex (HS.FuncDecl _ _ args expr) =
    let decArg = HS.UnQual (HS.Ident (HS.fromVarPat (args !! decArgIndex)))
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
    -- If one of the recursive functions is applied, there must be a
    -- structurally smaller variable in the decreasing position.
    checkExpr' (HS.Var _ name) args = case Map.lookup name decArgMap of
      Nothing -> True
      Just decArgIndex
        | decArgIndex >= length args -> False
        | otherwise -> case args !! decArgIndex of
          (HS.Var _ argName) -> argName `elem` smaller
          _                  -> False

    -- Function applications and @if@-expressions need to be checked
    -- recursively. In case of applications we also remember the
    -- arguments such that the case above can inspect the actual arguments.
    checkExpr' (HS.App _ e1 e2) args =
      checkExpr' e1 (e2 : args) && checkExpr' e2 []
    checkExpr' (HS.If _ e1 e2 e3) _ =
      checkExpr' e1 [] && checkExpr' e2 [] && checkExpr' e3 []

    -- @case@-expressions that match the decreasing argument or a variable
    -- that is structurally smaller than the decreasing argument, introduce
    -- new structurally smaller variables.
    checkExpr' (HS.Case _ expr alts) _ = case expr of
      (HS.Var _ varName) | varName == decArg || varName `Set.member` smaller ->
        all checkSmallerAlt alts
      _ -> all checkAlt alts

    -- The arguments of lambda expressions shadow existing (structurally
    -- smaller) variables
    checkExpr' (HS.Lambda _ args expr) _ =
      let smaller' = withoutArgs args smaller
      in  checkExpr decArg smaller' expr []

    -- Base expressions are
    checkExpr' (HS.Con _ _       ) _ = True
    checkExpr' (HS.Undefined _   ) _ = True
    checkExpr' (HS.ErrorExpr  _ _) _ = True
    checkExpr' (HS.IntLiteral _ _) _ = True

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
    withArgs args set =
      set `Set.union` Set.fromList
        (map (HS.UnQual . HS.Ident . HS.fromVarPat) args)

    -- | Removes the given variables to the set of structurally smaller
    --   variables (because they are shadowed by an argument from a lambda
    --   abstraction or @case@-alternative).
    withoutArgs :: [HS.VarPat] -> Set HS.QName -> Set HS.QName
    withoutArgs args set =
      set \\ Set.fromList (map (HS.UnQual . HS.Ident . HS.fromVarPat) args)

-- | Identifies the decreasing arguments of the given mutually recursive
--   function declarations.
--
--   Returns @Nothing@ if the decreasing argument could not be identified.
maybeIdentifyDecArgs :: [HS.FuncDecl] -> Maybe [Int]
maybeIdentifyDecArgs decls = find (checkDecArgs decls) (guessDecArgs decls)

-- | Identifies the decreasing arguments of the given mutually recursive
--   function declarations.
--
--   Reports a fatal error message, if the decreasing arguments could not be
--   identified.
identifyDecArgs :: [HS.FuncDecl] -> Converter [Int]
identifyDecArgs decls = maybe decArgError return (maybeIdentifyDecArgs decls)
 where
  decArgError :: Converter a
  decArgError =
    reportFatal
      $  Message (HS.getSrcSpan (head decls)) Error
      $  "Could not identify decreasing arguments of "
      ++ HS.prettyDeclIdents decls

-------------------------------------------------------------------------------
-- Constant arguments                                                        --
-------------------------------------------------------------------------------

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
        checkArg (HS.Var _ (HS.UnQual (HS.Ident name))) = name == x
        checkArg _ = False

        -- | Tests whether @x_j@ is passed unchanged as the @j@-th argument
        --   to every call to @g@ in the given expression.
        --
        --   The second argument contains the arguments that are passed to
        --   the current expression.
        checkExpr :: HS.Expr -> [HS.Expr] -> Bool

        -- If this is a call to @g@, check the @j@-th argument.
        checkExpr (HS.Var _ name) args
          | isG name  = j < length args && checkArg (args !! j)
          | otherwise = True

        -- If this is an application, check for calls to @g@ in the callee
        -- and argument.
        checkExpr (HS.App _ e1 e2) args =
          checkExpr e1 (e2 : args) && checkExpr e2 []

        -- The arguments passed to an @if@ or @case@ expression, are passed to
        -- all branches.
        -- If a pattern in a @case@ expression shadows @x_i@, @x_i@ is not
        -- left unchanged.
        checkExpr (HS.If _ e1 e2 e3) args =
          checkExpr e1 [] && checkExpr e2 args && checkExpr e3 args
        checkExpr (HS.Case _ expr alts) args =
          checkExpr expr [] && all (flip checkAlt args) alts

        -- No beta reduction is applied when a lambda expression is
        -- encountered, but the right-hand side still needs to be checked.
        -- If an argument shadows @x_i@ and there are calls to @g@ on the
        -- right hand side, @x_i@ is not left unchanged.
        checkExpr (HS.Lambda _ args expr) _
          | x `shadowedBy` args = not (callsG expr)
          | otherwise           = checkExpr expr []

        -- Constructors, literals and error terms cannot contain further
        -- calls to @g@.
        checkExpr (HS.Con        _ _) _ = True
        checkExpr (HS.IntLiteral _ _) _ = True
        checkExpr (HS.Undefined _   ) _ = True
        checkExpr (HS.ErrorExpr _ _ ) _ = True

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
        shadowedBy = flip (flip elem . map HS.fromVarPat)
      guard (checkExpr rhs [])
      -- Add edge if the test was successful.
      return (g, y)
  return (node, node, adjacent)
 where
  nodes :: [(CGNode, Int, HS.Expr)]
  nodes = do
    (HS.FuncDecl _ declIdent args rhs) <- decls
    let funName = HS.fromDeclIdent declIdent
    (argName, argIndex) <- zip (map HS.fromVarPat args) [0 ..]
    return ((funName, argName), argIndex, rhs)

-- | Identifies function arguments that can be moved to a @Section@
--   sentence in Coq.
--
--   The call graph of the given function declarations should be strongly
--   connected.
identifyConstArgs :: [HS.FuncDecl] -> Converter ()
identifyConstArgs decls = do
  modName <- inEnv envModName
  identifyConstArgs' modName decls

-- | Like 'identifyConstArgs' but takes the name of the currently translated
--   module as an argument.
identifyConstArgs' :: HS.ModName -> [HS.FuncDecl] -> Converter ()
identifyConstArgs' modName decls = do
  let constArgs =
        filter checkSCC $ catMaybes $ map fromCyclicSCC $ stronglyConnComp
          constArgGraph
  report
    $ Message NoSrcSpan Info
    $ ("Const arguments for " ++ show funcNames ++ ": " ++ show constArgs)
  return ()
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
      -- If there is an edge from @f@ to @g@ in the call graph...
      guard (dependsDirectlyOn callGraph f' g')
      -- ... there must also be an edge in the constant argument graph.
      adjacent <- maybeToList (Map.lookup (f, x) constArgMap)
      return ((g, y) `elem` adjacent)

  -- | The names of all given function declarations.
  funcNames :: [String]
  funcNames = map (HS.fromDeclIdent . HS.getDeclIdent) decls

  -- | Tests whether the given list of nodes contains one node for every
  --   function declaration.
  containsAllFunctions :: [CGNode] -> Bool
  containsAllFunctions nodes =
    length nodes == length decls && all (`elem` (map fst nodes)) funcNames

  -- | Gets the nodes of a cyclic strongly connected component.
  fromCyclicSCC :: SCC CGNode -> Maybe [CGNode]
  fromCyclicSCC (AcyclicSCC _    ) = Nothing
  fromCyclicSCC (CyclicSCC  nodes) = Just nodes
