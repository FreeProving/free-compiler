-- | This module contains data types and function for working with subterms
--   of Haskell expressions.

module Compiler.Haskell.Subterm
  ( -- * Positions
    Pos(..)
  , rootPos
  , pos
  , above
  , below
  , leftOf
  , rightOf
    -- * Subterms
  , selectSubterm
  , replaceSubterm
  , replaceSubterms
    -- * Searching for subterms
  , findSubtermPos
  , findSubterms
    -- * Bound variables
  , boundVarsAt
  , usedVarsAt
  )
where

import           Data.Composition               ( (.:) )
import           Data.List                      ( intersperse
                                                , isPrefixOf
                                                )
import           Data.Maybe                     ( fromJust )
import qualified Data.Set                      as Set
import           Data.Set                       ( Set )

import           Compiler.Analysis.DependencyExtraction
import           Compiler.Pretty
import           Compiler.Haskell.AST          as HS

-------------------------------------------------------------------------------
-- Direct children                                                           --
-------------------------------------------------------------------------------

-- | Gets the direct child expression nodes of the given expression.
childExprs :: HS.Expr -> [HS.Expr]
childExprs (HS.App _ e1 e2       ) = [e1, e2]
childExprs (HS.If _ e1 e2 e3     ) = [e1, e2, e3]
childExprs (HS.Case   _ expr alts) = expr : map altChildExpr alts
childExprs (HS.Lambda _ _    expr) = [expr]
childExprs (HS.Con _ _           ) = []
childExprs (HS.Var _ _           ) = []
childExprs (HS.Undefined _       ) = []
childExprs (HS.ErrorExpr  _ _    ) = []
childExprs (HS.IntLiteral _ _    ) = []

-- | Gets the expression on the right hand side of the given @case@-expression
--   alternative.
altChildExpr :: HS.Alt -> HS.Expr
altChildExpr (HS.Alt _ _ _ expr) = expr

-- | Replaces all direct child expression nodes of the given expression.
replaceChildExprs :: HS.Expr -> [HS.Expr] -> Maybe HS.Expr
replaceChildExprs (HS.App srcSpan _ _) [e1', e2'] =
  Just (HS.App srcSpan e1' e2')
replaceChildExprs (HS.If srcSpan _ _ _) [e1', e2', e3'] =
  Just (HS.If srcSpan e1' e2' e3')
replaceChildExprs (HS.Case srcSpan _ alts) (expr' : altChildren')
  | length alts == length altChildren' = Just
    (HS.Case srcSpan expr' (zipWith replaceAltChildExpr alts altChildren'))
replaceChildExprs (HS.Lambda srcSpan args _) [expr'] =
  Just (HS.Lambda srcSpan args expr')
replaceChildExprs expr@(HS.Con _ _       ) [] = Just expr
replaceChildExprs expr@(HS.Var _ _       ) [] = Just expr
replaceChildExprs expr@(HS.Undefined _   ) [] = Just expr
replaceChildExprs expr@(HS.ErrorExpr  _ _) [] = Just expr
replaceChildExprs expr@(HS.IntLiteral _ _) [] = Just expr
replaceChildExprs _                        _  = Nothing

-- | Replaces the expression on the right hand side of the given
--   @case@-expression alternative.
replaceAltChildExpr :: HS.Alt -> HS.Expr -> HS.Alt
replaceAltChildExpr (HS.Alt srcSpan varPat conPat _) expr' =
  HS.Alt srcSpan varPat conPat expr'

-------------------------------------------------------------------------------
-- Positions                                                                 --
-------------------------------------------------------------------------------

-- | Describes a position of a subterm within a Haskell expression.
data Pos = Pos [Int]
  deriving (Eq, Show)

-- | Pretty prints a position.
instance Pretty Pos where
  pretty (Pos xs) =
    char '<' <> hcat (intersperse (char '.') (map int xs)) <> char '>'

-- | Position of the root expression.
rootPos :: Pos
rootPos = Pos []

-- | Gets all valid positions of subterms within the given Haskell expression.
pos :: HS.Expr -> [Pos]
pos expr = rootPos
  : concat (zipWith (map . consPos) [1 .. length children] (map pos children))
 where
  children :: [HS.Expr]
  children = childExprs expr

  -- | Adds the given element to the front of a position.
  consPos :: Int -> Pos -> Pos
  consPos x (Pos xs) = Pos (x : xs)

-- Tests whether a position is above another one.
above :: Pos -> Pos -> Bool
above (Pos ps1) (Pos ps2) = ps1 `isPrefixOf` ps2

-- Tests whether a position is below another one.
below :: Pos -> Pos -> Bool
below = flip above

-- Tests whether a position is left of another one.
leftOf :: Pos -> Pos -> Bool
leftOf (Pos [])         _                = False
leftOf _                (Pos []        ) = False
leftOf (Pos (p1 : ps1)) (Pos (p2 : ps2)) = case compare p1 p2 of
  LT -> True
  EQ -> leftOf (Pos ps1) (Pos ps2)
  GT -> False

-- Tests whether a position is right of another one.
rightOf :: Pos -> Pos -> Bool
rightOf = flip leftOf

-------------------------------------------------------------------------------
-- Subterms                                                                  --
-------------------------------------------------------------------------------

-- | Selects a subterm of the given expression at the specified position.
--
--   Returns @Nothing@ if there is no such subterm.
selectSubterm :: HS.Expr -> Pos -> Maybe HS.Expr
selectSubterm expr (Pos []) = Just expr
selectSubterm expr (Pos (p : ps))
  | p <= 0 || p > length children = Nothing
  | otherwise                     = selectSubterm (children !! (p - 1)) (Pos ps)
 where
  children :: [HS.Expr]
  children = childExprs expr

-- | Replaces a subterm of the given expression at the specified position
--   with another expression.
--
--   Returns @Nothing@ if there is no such subterm.
replaceSubterm
  :: HS.Expr -- ^ The expression whose subterm to replace.
  -> Pos     -- ^ The position of the subterm.
  -> HS.Expr -- ^ The expression to replace the subterm with.
  -> Maybe HS.Expr
replaceSubterm _ (Pos []) expr' = Just expr'
replaceSubterm expr (Pos (p : ps)) expr'
  | p <= 0 || p > length children = Nothing
  | otherwise = do
    let (before, child : after) = splitAt (p - 1) children
    child' <- replaceSubterm child (Pos ps) expr'
    replaceChildExprs expr (before ++ child' : after)
 where
  children :: [HS.Expr]
  children = childExprs expr

-- | Replaces all subterms at the given positions with other expressions.
--
--   Returns @Nothing@ if any of the subterms could not be replaced
replaceSubterms :: HS.Expr -> [(Pos, HS.Expr)] -> Maybe HS.Expr
replaceSubterms expr []             = return expr
replaceSubterms expr ((p, e) : pes) = do
  expr' <- replaceSubterm expr p e
  replaceSubterms expr' pes

-------------------------------------------------------------------------------
-- Searching for subterms                                                    --
-------------------------------------------------------------------------------

-- | Gets a list of positions for subterms of the given expression that
--   satisfy the provided predicate.
findSubtermPos :: (HS.Expr -> Bool) -> HS.Expr -> [Pos]
findSubtermPos predicate expr =
  filter (predicate . fromJust . selectSubterm expr) (pos expr)

-- | Gets a list of subterms of the given expression that satisfy the
--   provided predicate.
findSubterms :: (HS.Expr -> Bool) -> HS.Expr -> [HS.Expr]
findSubterms predicate expr =
  filter predicate (map (fromJust . selectSubterm expr) (pos expr))

-------------------------------------------------------------------------------
-- Bound variables                                                           --
-------------------------------------------------------------------------------

-- | Gets the names of variables that are bound by lambda abstractions or
--   variable patterns in @case@-expressions at the given position of an
--   expression.
--
--   Returns the empty set if the position is invalid.
boundVarsAt :: HS.Expr -> Pos -> Set HS.QName
boundVarsAt = maybe Set.empty id .: boundVarsAt'
 where
  boundVarsAt' :: HS.Expr -> Pos -> Maybe (Set HS.QName)
  boundVarsAt' _    (Pos []      ) = return Set.empty
  boundVarsAt' expr (Pos (p : ps)) = do
    child <- selectSubterm expr (Pos [p])
    bvars <- boundVarsAt' child (Pos ps)
    case expr of
      (HS.Case _ _ alts) | p > 1 -> do
        let altVars = altBoundVars (alts !! (p - 2))
        return (bvars `Set.union` altVars)
      (HS.Lambda _ args _) -> return (bvars `Set.union` fromVarPats args)
      _                    -> return bvars

  -- | Gets the names of variables bound by the variable patterns of the given
  --   @case@-expression alternative.
  altBoundVars :: HS.Alt -> Set HS.QName
  altBoundVars (HS.Alt _ _ varPats _) = fromVarPats varPats

  -- | Converts a list of variable patterns to a set of variable names bound
  --   by these patterns.
  fromVarPats :: [HS.VarPat] -> Set HS.QName
  fromVarPats = Set.fromList . map (HS.UnQual . HS.Ident . HS.fromVarPat)

-- | Gets the names of variables that are used by the subterm t the given
--   position.
--
--   The returned set also contains function and argument names.
--   To get a set of variable names only, intersect the result with
--   'boundVarsAt'.
--
--   Returns the empty set if the position is invalid.
usedVarsAt :: HS.Expr -> Pos -> Set HS.QName
usedVarsAt = maybe Set.empty id .: usedVarsAt'
 where
  usedVarsAt' :: HS.Expr -> Pos -> Maybe (Set HS.QName)
  usedVarsAt' expr p = do
    subterm <- selectSubterm expr p
    return (varSet subterm)
