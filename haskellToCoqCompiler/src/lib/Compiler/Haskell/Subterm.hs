-- | This module contains data types and function for working with subterms
--   of Haskell expressions.

module Compiler.Haskell.Subterm
  ( -- * Positions
    Pos(..)
  , rootPos
  , pos
    -- * Subterms
  , selectSubterm
  , replaceSubterm
    -- * Searching for subterms
  , findSubtermPos
  , findSubterms
  )
where

import           Data.List                      ( intersperse )
import           Data.Maybe                     ( fromJust )

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

-- Describes a position of a subterm within a Haskell expression.
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
