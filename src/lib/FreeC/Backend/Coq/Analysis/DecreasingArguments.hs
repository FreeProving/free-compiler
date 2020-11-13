-- | This module contains the termination checker for the intermediate
--   language. The goal is to to find one argument for every recursive
--   function whose size is reduced in every recursive call. If such
--   arguments exist we know that the function will terminate and can
--   be translated to Coq. The termination checker defined in this
--   module is very limited compared to Coq's termination checker.
--   Even if we don't recognize the decreasing arguments, Coq might
--   still be able to tell that the function is decreasing on one of
--   its arguments. However, we cannot rely on Coq's termination
--   entirely, since we need to know the decreasing arguments for
--   the transformation of recursive functions into a recursive
--   helper function and a non-recursive main function (see also
--   "FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithHelpers")
--
--   == Guessing Decreasing Arguments
--
--   Given set of mutually recursive function declarations @F@, the
--   termination checker tries to find a combination of arguments such
--   that each function in the set decreases on the corresponding argument.
--   Since we have to know the decreasing argument of all functions in the
--   set in order to test whether a function decreases on one of its argument,
--   we first enumerate (or /guess/) all possible combinations and then check
--   whether the combination of decreasing arguments is valid.
--
--   == Checking Decreasing Arguments
--
--   A function @f ∈ F@ declared by
--
--   > f x₁ … xᵢ … xₙ = e
--
--   decreases on its @i@-th argument if for every recursive call to
--   functions @g ∈ F@ on the right-hand side @e@ of @f@
--
--   > g e₁ … eⱼ … eₘ
--
--   where @j@ is the decreasing argument guessed for @g@ the expression
--   @eⱼ@ is recognized as structurally smaller than @xᵢ@.
--
--   == Checking for Structurally Smaller Expressions
--
--   To test whether an expression is structurally smaller than the decreasing
--   argument, we assign every expression a depth within the structure of the
--   decreasing argument as described below. There is a special depth value @⊥@
--   with the property @⊥ + 1 = ⊥@ that is assigned to expressions that are not
--   known to be subterms of the decreasing argument.
--
--   1. The decreasing argument itself is at depth @0@.
--
--   2. The variables @x₁, …, xₙ@ that are bound by an alternative
--      @case e of { … ; C x₁ … xₙ -> e' ; … }@ of a @case@-expression whose
--      scrutinee @e@ is at depth @d@ are at depth @d + 1@ within the right-
--      hand side @e@ of the alternative.
--
--   3. The variables @x₁, …, xₙ@ that are bound by a @let@-binding
--      @let { x₁ = e₁ ; … ; xₙ = eₙ } in e@ whose right-hand sides @e₁, …, eₙ@
--      are at depths @d₁, …, dₙ@ are at the same depths within the @in@-
--      expression @e@ as well as in the right-hand sides @e₁, …, eₙ@.
--
--   4. All other variables and non-variable expressions are at depth @⊥@.
--
--   An expression is structurally smaller than the decreasing argument if
--   its depth is greater than the depth of the decreasing argument, i.e., @>0@.
--   The definition above ensures that
--
--    * variables that are introduced by @case@-expression alternatives are
--      structurally smaller than the scrutinee of the @case@-expression and
--    * variables that are introduced by @let@-bindings are structually equal
--      to their right-hand side.
--
--   == Bypassing the Termination Checker
--
--   Coq's termination checker uses the same idea as described above but
--   is much more sophisticated. If the user knows that their function
--   declaration is decreasing on one of its arguments, they can annotate
--   the decreasing argument using a custom pragma (see also
--   'FreeC.IR.Syntax.Pragma.DecArgPragma'). If there is such an annotation
--   'guessDecArgs' will not consider any other argument for the annotated
--   function declaration and 'checkDecArgs' always accepts the guessed
--   argument as a decreasing argument.
module FreeC.Backend.Coq.Analysis.DecreasingArguments
  ( DecArgIndex
  , identifyDecArgs
    -- * Depth Map
  , DepthMap
  , lookupDepth
  , initDepthMap
  , depthMapAt
  , mapChildrenWithDepthMaps
  ) where

import           Data.List             ( find )
import           Data.Map.Strict       ( Map )
import qualified Data.Map.Strict       as Map
import           Data.Maybe            ( mapMaybe )
import qualified Data.Set              as Set
import           Data.Tuple.Extra      ( uncurry3 )

import           FreeC.Environment
import           FreeC.IR.Subterm
import qualified FreeC.IR.Syntax       as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Guessing Decreasing Arguments                                             --
-------------------------------------------------------------------------------
-- | Type for the index of a decreasing argument.
type DecArgIndex = Int

-- | Guesses all possible combinations of decreasing arguments for the given
--   mutually recursive function declarations.
--
--   The second argument contains the known decreasing arguments as specified
--   by the user.
--
--   Returns a list of all possible combinations of argument indices.
guessDecArgs :: [IR.FuncDecl] -> [Maybe DecArgIndex] -> [[DecArgIndex]]
guessDecArgs [] _ = return []
guessDecArgs _ [] = return []
guessDecArgs (_ : decls) (Just decArgIndex : knownDecArgIndecies) = do
  decArgIndecies <- guessDecArgs decls knownDecArgIndecies
  return (decArgIndex : decArgIndecies)
guessDecArgs (decl : decls) (Nothing : knownDecArgIndecies) = do
  let arity = length (IR.funcDeclArgs decl)
  decArgIndecies <- guessDecArgs decls knownDecArgIndecies
  decArgIndex <- [0 .. arity - 1]
  return (decArgIndex : decArgIndecies)

-------------------------------------------------------------------------------
-- Checking Decreasing Arguments                                             --
-------------------------------------------------------------------------------
-- | Tests whether the given combination of choices for the decreasing
--   arguments of function declarations in a strongly connected component
--   is valid (i.e. all function declarations actually decrease the
--   corresponding argument).
--
--   The second argument contains the known decreasing arguments as specified
--   by the user. If the user has specified the decreasing argument of a
--   function it is not checked whether the function actually decreases on the
--   argument (such that the user is not limited by our termination checker).
checkDecArgs :: [IR.FuncDecl] -> [Maybe DecArgIndex] -> [DecArgIndex] -> Bool
checkDecArgs decls knownDecArgIndecies decArgIndecies = all
  (uncurry3 checkDecArg) (zip3 knownDecArgIndecies decArgIndecies decls)
 where
  -- | Maps the names of functions in the strongly connected component
  --   to the index of their decreasing argument.
  decArgMap :: Map IR.QName DecArgIndex
  decArgMap = foldr (uncurry insertFuncDecl) Map.empty
    (zip decls decArgIndecies)

  -- | Inserts a function declaration with the given decreasing argument index
  --   into 'decArgMap'.
  insertFuncDecl :: IR.FuncDecl
                 -> DecArgIndex
                 -> Map IR.QName DecArgIndex
                 -> Map IR.QName DecArgIndex
  insertFuncDecl = Map.insert . IR.funcDeclQName

  -- | Tests whether the given function declaration actually decreases on the
  --   argument with the given index.
  --
  --   The first argument is the index of the decreasing argument as specified
  --   by the user or @Nothing@ if there is no such annotation.
  checkDecArg :: Maybe DecArgIndex -> DecArgIndex -> IR.FuncDecl -> Bool
  checkDecArg (Just _) _ _ = True
  checkDecArg _ decArgIndex (IR.FuncDecl _ _ _ args _ rhs)
    = let decArg = IR.varPatQName (args !! decArgIndex)
      in checkExpr (initDepthMap decArg) rhs

  -- | Tests whether there is a variable that is structurally smaller than the
  --   potential decreasing argument in the position of the decreasing argument
  --   for all applications of functions from the strongly connected component.
  --
  --   The first argument maps variables that are known to be structurally
  --   smaller or equal than the decreasing argument of the function whose
  --   right-hand side is checked to their depth within the structure. The
  --   decreasing argument itself and its aliases have a depth of @0@.
  checkExpr :: DepthMap -> IR.Expr -> Bool
  checkExpr depthMap = flip checkExpr' []
   where
    -- | Tests whether the given expression is structurally smaller than the
    --   decreasing argument.
    isSmaller :: IR.Expr -> Bool
    isSmaller = any (> 0) . flip lookupDepth depthMap

    -- | Like 'checkExpr' but the arguments the expression is applied to are
    --   accumulated in the second argument.
    checkExpr' :: IR.Expr -> [IR.Expr] -> Bool

    -- If one of the recursive functions is applied, there must be a
    -- structurally smaller variable in the decreasing position.
    checkExpr' (IR.Var _ name _) args = case Map.lookup name decArgMap of
      Nothing          -> True
      Just decArgIndex | decArgIndex >= length args -> False
                       | otherwise -> isSmaller (args !! decArgIndex)
    -- The arguments that an expression is applied to are accumulated in the
    -- second argument. The argument still needs to be checked recursively
    -- because it could contain recursive calls as well.
    checkExpr' (IR.App _ e1 e2 _) args = checkExpr' e1 (e2 : args)
      && checkExpr' e2 []
    -- Visible type applications forward the arguments to the actually applied
    -- function expression.
    checkExpr' (IR.TypeAppExpr _ expr _ _) args = checkExpr' expr args
    -- Check all other expressions recursively and extend the 'depthMap' if
    -- there are variable binders. Arguments are not passed to subterms.
    checkExpr' expr _ = and (mapChildrenWithDepthMaps checkExpr depthMap expr)

-------------------------------------------------------------------------------
-- Depth Map                                                                 --
-------------------------------------------------------------------------------
-- | A map that maps the names of variables to their depth within the structure
--   of a potential decreasing argument.
--
--   This map contains @0@ for variables that are structurally equal to the
--   decreasing argument. If it is not known how whether a variable is a
--   subterm of the decreasing argument, there is no entry.
type DepthMap = Map IR.QName Int

-- | Gets the depth of an expression within the structure of the decreasing
--   argument.
--
--   Returns @Nothing@ if the given expression it is not a subterm of the
--   decreasing argument. The decreasing argument itself and its aliases
--   have a depth of @0@.
lookupDepth :: IR.Expr -> DepthMap -> Maybe Int
lookupDepth (IR.Var _ varName _) = Map.lookup varName
lookupDepth _                    = const Nothing

-- | Sets the depth of the variable that is bound by the given pattern
--   or removes the entry from the given 'DepthMap' if the new depth is
--   @Nothing@.
withDepth :: IR.VarPat -> Maybe Int -> DepthMap -> DepthMap
withDepth varPat maybeDepth = Map.alter (const maybeDepth)
  (IR.varPatQName varPat)

-- | Sets the depths of the variables that are bound by the given patterns
--   or removes the corresponding entries from the given 'DepthMap' if the new
--   depth is @Nothing@.
withDepths :: [(IR.VarPat, Maybe Int)] -> DepthMap -> DepthMap
withDepths = flip (foldr (uncurry withDepth))

-- | Removes the given variables from the set of structurally smaller or equal
--   variables of the given 'DepthMap' (for example, because they are shadowed
--   by an argument from a lambda abstraction).
withoutArgs :: [IR.VarPat] -> DepthMap -> DepthMap
withoutArgs = flip Map.withoutKeys . Set.fromList . map IR.varPatQName

-- | Creates the initial 'DepthMap' for the given decreasing argument.
initDepthMap :: IR.QName -> DepthMap
initDepthMap decArg = Map.singleton decArg 0

-- | Builds a 'DepthMap' for variables that are bound at the given position
--   in the given expression.
depthMapAt
  :: Pos      -- ^ The position within the root expression to build the map for.
  -> IR.Expr  -- ^ The root expression.
  -> IR.QName -- ^ The name of the decreasing argument.
  -> DepthMap
depthMapAt p expr decArg = foldr (uncurry extendDepthMap) (initDepthMap decArg)
  (mapMaybe selectParent (ancestorPos p))
 where
  -- | Gets the subterm at the parent position of the given position as well
  --   as the index (starting at @1@) of the position within its parent
  --   position.
  selectParent :: Pos -> Maybe (Int, IR.Expr)
  selectParent = fmap (fmap (selectSubterm' expr)) . parentPos'

-- | Applies the given function to the children of the given expression
--   and the extended 'DepthMap' for that child.
mapChildrenWithDepthMaps
  :: (DepthMap -> IR.Expr -> a) -> DepthMap -> IR.Expr -> [a]
mapChildrenWithDepthMaps f depthMap expr
  = let children   = childTerms expr
        indicies   = [1 .. length children]
        depthMaps' = map (($ depthMap) . flip extendDepthMap expr) indicies
    in zipWith f depthMaps' children

-- | Updates the given 'DepthMap' for binders that bind variables in the child
--   expression with the given index (starting at @1@) in the given expression.
extendDepthMap :: Int -> IR.Expr -> DepthMap -> DepthMap

-- The bindings of @let@-expressions introduce variables at the same depth
-- as the expressions on their right-hand sides.
extendDepthMap _ (IR.Let _ binds _ _) depthMap
  = let shadowed  = Set.fromList (map IR.declQName binds)
        depthMap' = depthMap `Map.withoutKeys` shadowed
    in extendBindDepths depthMap'
 where
  -- | Recursively extends the given depth map by the depths of variables
  --   declared by the @let@-bindings until the depths don't change anymore.
  --
  --   Without recursion @let@-expressions of the form
  --
  --   > let { x = y; y = z } in e
  --
  --   would set @y@ at the same depth as @z@ but @x@ not.
  extendBindDepths :: DepthMap -> DepthMap
  extendBindDepths depthMap
    = let bindDepths = map (flip lookupDepth depthMap . IR.bindExpr) binds
          bindPats   = map IR.bindVarPat binds
          depthMap'  = withDepths (zip bindPats bindDepths) depthMap
      in if depthMap == depthMap'
           then depthMap'
           else extendBindDepths depthMap'
-- Alternatives of @case@-expressions introduce variables at a depth one
-- level deeper than the scrutinee.
extendDepthMap childIndex (IR.Case _ scrutinee alts _) depthMap
  | childIndex == 1 = depthMap
  | otherwise = let srutineeDepth = lookupDepth scrutinee depthMap
                    varDepths     = repeat (succ <$> srutineeDepth)
                    varPats       = IR.altVarPats (alts !! (childIndex - 2))
                in withDepths (zip varPats varDepths) depthMap
-- The depth of arguments of lambda expressions is unknown.
extendDepthMap _ (IR.Lambda _ args _ _) depthMap = withoutArgs args depthMap
-- All other expressions don't introduce variables.
extendDepthMap _ (IR.Var _ _ _) depthMap = depthMap
extendDepthMap _ (IR.Con _ _ _) depthMap = depthMap
extendDepthMap _ (IR.App _ _ _ _) depthMap = depthMap
extendDepthMap _ (IR.TypeAppExpr _ _ _ _) depthMap = depthMap
extendDepthMap _ (IR.If _ _ _ _ _) depthMap = depthMap
extendDepthMap _ (IR.Undefined _ _) depthMap = depthMap
extendDepthMap _ (IR.ErrorExpr _ _ _) depthMap = depthMap
extendDepthMap _ (IR.Trace _ _ _ _) depthMap = depthMap
extendDepthMap _ (IR.IntLiteral _ _ _) depthMap = depthMap

-------------------------------------------------------------------------------
-- Identifying Decreasing Arguments                                          --
-------------------------------------------------------------------------------
-- | Identifies the decreasing arguments of the given mutually recursive
--   function declarations.
--
--   The second argument contains the known decreasing arguments as specified
--   by the user.
--
--   Returns @Nothing@ if the decreasing argument could not be identified.
maybeIdentifyDecArgs
  :: [IR.FuncDecl] -> [Maybe DecArgIndex] -> Maybe [DecArgIndex]
maybeIdentifyDecArgs decls knownDecArgIndecies = find
  (checkDecArgs decls knownDecArgIndecies)
  (guessDecArgs decls knownDecArgIndecies)

-- | Identifies the decreasing arguments of the given mutually recursive
--   function declarations.
--
--   Reports a fatal error message, if the decreasing arguments could not be
--   identified.
identifyDecArgs :: [IR.FuncDecl] -> Converter [DecArgIndex]
identifyDecArgs decls = do
  knownDecArgIndecies <- mapM lookupDecArgIndexOfDecl decls
  maybe decArgError return (maybeIdentifyDecArgs decls knownDecArgIndecies)
 where
  -- | Looks up the index of an annotated decreasing argument.
  lookupDecArgIndexOfDecl :: IR.FuncDecl -> Converter (Maybe Int)
  lookupDecArgIndexOfDecl = inEnv . lookupDecArgIndex . IR.funcDeclQName

  -- | Prints an error message if the decreasing arguments could not
  --   be identified.
  decArgError :: Converter a
  decArgError = reportFatal
    $ Message (IR.funcDeclSrcSpan (head decls)) Error
    $ unlines
    [ "Could not identify decreasing arguments of "
        ++ showPretty (map IR.funcDeclIdent decls)
        ++ "."
    , "Consider adding a {-# FreeC <function> DECREASES ON <argument> #-} "
        ++ "annotation."
    ]
