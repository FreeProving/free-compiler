-- | This module contains data types and function for working with subterms
--   of expressions and type expressions.
--
--   There are also functions for finding the names and types of variables that
--   are bound at a given position in an expression.

module FreeC.IR.Subterm
  ( -- * Direct children
    childTerms
  , replaceChildTerms
    -- * Positions
  , Pos(..)
  , rootPos
  , consPos
  , parentPos
  , allPos
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
  , boundVarsWithTypeAt
  )
where

import           Data.Composition               ( (.:) )
import           Data.List                      ( intersperse
                                                , isPrefixOf
                                                )
import           Data.Maybe                     ( fromJust
                                                , fromMaybe
                                                )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Set                       ( Set )
import           Data.Tuple.Extra               ( (&&&) )

import qualified FreeC.IR.Syntax               as IR
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Utility functions                                                         --
-------------------------------------------------------------------------------

-- | Runs the given function on if the given list has the specified number of
--   arguments.
--
--   Returns the function's result of @Nothing@ if the list has the wrong
--   number of elements.
checkArity :: Int -> ([a] -> b) -> [a] -> Maybe b
checkArity n f xs | length xs == n = Just (f xs)
                  | otherwise      = Nothing

-- | Like 'checkArity' for functions that do no expect any arguments.
nullary :: b -> [a] -> Maybe b
nullary y xs | null xs   = Just y
             | otherwise = Nothing

-------------------------------------------------------------------------------
-- Direct children                                                           --
-------------------------------------------------------------------------------

-- | Type class for AST nodes with child nodes of the same type.
class Subterm a where
  -- | Gets the child nodes of the given AST node.
  childTerms :: a -> [a]

  -- | Replaces the child nodes of the given AST node.
  replaceChildTerms :: a -> [a] -> Maybe a

-- | Expressions have subterms.
instance Subterm IR.Expr where
  -- | Gets the direct child expression nodes of the given expression.
  childTerms (IR.App         _ e1   e2 _) = [e1, e2]
  childTerms (IR.TypeAppExpr _ expr _  _) = [expr]
  childTerms (IR.If _ e1 e2 e3 _        ) = [e1, e2, e3]
  childTerms (IR.Case   _ expr alts _   ) = expr : map IR.altRhs alts
  childTerms (IR.Lambda _ _    expr _   ) = [expr]
  childTerms (IR.Con _ _ _              ) = []
  childTerms (IR.Var _ _ _              ) = []
  childTerms (IR.Undefined _ _          ) = []
  childTerms (IR.ErrorExpr  _ _ _       ) = []
  childTerms (IR.IntLiteral _ _ _       ) = []

  -- | Replaces all direct child expression nodes of the given expression.
  replaceChildTerms (IR.App srcSpan _ _ exprType) =
    checkArity 2 $ \[e1', e2'] -> IR.App srcSpan e1' e2' exprType

  replaceChildTerms (IR.TypeAppExpr srcSpan _ typeExpr exprType) =
    checkArity 1 $ \[expr'] -> IR.TypeAppExpr srcSpan expr' typeExpr exprType

  replaceChildTerms (IR.If srcSpan _ _ _ exprType) =
    checkArity 3 $ \[e1', e2', e3'] -> IR.If srcSpan e1' e2' e3' exprType

  replaceChildTerms (IR.Case srcSpan _ alts exprType) =
    checkArity (length alts + 1) $ \(expr' : altChildren') -> IR.Case
      srcSpan
      expr'
      (zipWith replaceAltChildExpr alts altChildren')
      exprType
   where
    -- | Replaces the expression on the right hand side of the given
    --   @case@-expression alternative.
    replaceAltChildExpr :: IR.Alt -> IR.Expr -> IR.Alt
    replaceAltChildExpr alt rhs' = alt { IR.altRhs = rhs' }

  replaceChildTerms (IR.Lambda srcSpan args _ exprType) =
    checkArity 1 $ \[expr'] -> IR.Lambda srcSpan args expr' exprType

  replaceChildTerms expr@(IR.Con _ _ _       ) = nullary expr
  replaceChildTerms expr@(IR.Var _ _ _       ) = nullary expr
  replaceChildTerms expr@(IR.Undefined _ _   ) = nullary expr
  replaceChildTerms expr@(IR.ErrorExpr  _ _ _) = nullary expr
  replaceChildTerms expr@(IR.IntLiteral _ _ _) = nullary expr

-- | Type expressions have subterms.
instance Subterm IR.Type where
  -- | Gets the direct child type expression nodes of the given type
  --   expression.
  childTerms (IR.TypeVar _ _     ) = []
  childTerms (IR.TypeCon _ _     ) = []
  childTerms (IR.TypeApp  _ t1 t2) = [t1, t2]
  childTerms (IR.FuncType _ t1 t2) = [t1, t2]

  -- | Replaces all direct child type expression nodes of the given type
  --   expression.
  replaceChildTerms typeExpr@(IR.TypeVar _ _) = nullary typeExpr
  replaceChildTerms typeExpr@(IR.TypeCon _ _) = nullary typeExpr
  replaceChildTerms (IR.TypeApp srcSpan _ _) =
    checkArity 2 $ \[t1', t2'] -> IR.TypeApp srcSpan t1' t2'
  replaceChildTerms (IR.FuncType srcSpan _ _) =
    checkArity 2 $ \[t1', t2'] -> IR.FuncType srcSpan t1' t2'

-------------------------------------------------------------------------------
-- Positions                                                                 --
-------------------------------------------------------------------------------

-- | Describes a position of a subterm within a Haskell expression.
newtype Pos = Pos [Int]
  deriving (Eq, Show)

-- | Pretty prints a position.
instance Pretty Pos where
  pretty (Pos xs) =
    char '<' <> hcat (intersperse (char '.') (map int xs)) <> char '>'

-- | Position of the root expression.
rootPos :: Pos
rootPos = Pos []

-- | Extends an position inside of a child node to a position inside of a
--   parent node.
--
--   If @pos@ is the position of a subterm @s@ of an expression or
--   type expression @tᵢ@, then @consPos i pos@ is the position of
--   the subterm @s@ of a term @C t₁ ... tᵢ ... tₙ@.
consPos :: Int -> Pos -> Pos
consPos p (Pos ps) = Pos (p : ps)

-- | Gets the parent position or @Nothing@ if the given position is the
--   root position.
parentPos :: Pos -> Maybe Pos
parentPos (Pos ps) | null ps   = Nothing
                   | otherwise = Just (Pos (init ps))

-- | Gets all valid positions of subterms within the given Haskell expression.
allPos :: Subterm a => a -> [Pos]
allPos term =
  rootPos
    : [ consPos p childPos
      | (p, child) <- zip [1 ..] (childTerms term)
      , childPos   <- allPos child
      ]

-- | Tests whether a position is above another one.
above :: Pos -> Pos -> Bool
above (Pos ps1) (Pos ps2) = ps1 `isPrefixOf` ps2

-- | Tests whether a position is below another one.
below :: Pos -> Pos -> Bool
below = flip above

-- | Tests whether a position is left of another one.
leftOf :: Pos -> Pos -> Bool
leftOf (Pos [])         _                = False
leftOf _                (Pos []        ) = False
leftOf (Pos (p1 : ps1)) (Pos (p2 : ps2)) = case compare p1 p2 of
  LT -> True
  EQ -> leftOf (Pos ps1) (Pos ps2)
  GT -> False

-- | Tests whether a position is right of another one.
rightOf :: Pos -> Pos -> Bool
rightOf = flip leftOf

-------------------------------------------------------------------------------
-- Subterms                                                                  --
-------------------------------------------------------------------------------

-- | Selects a subterm of the given expression at the specified position.
--
--   Returns @Nothing@ if there is no such subterm.
selectSubterm :: Subterm a => a -> Pos -> Maybe a
selectSubterm term (Pos []) = Just term
selectSubterm term (Pos (p : ps))
  | p <= 0 || p > length children = Nothing
  | otherwise                     = selectSubterm (children !! (p - 1)) (Pos ps)
  where
  -- children :: [a]
        children = childTerms term

-- | Replaces a subterm of the given expression or type expression at the
--   specified position with another expression.
--
--   Returns @Nothing@ if there is no such subterm.
replaceSubterm
  :: Subterm a
  => a       -- ^ The (type) expression whose subterm to replace.
  -> Pos     -- ^ The position of the subterm.
  -> a       -- ^ The (type) expression to replace the subterm with.
  -> Maybe a
replaceSubterm _ (Pos []) term' = Just term'
replaceSubterm term (Pos (p : ps)) term'
  | p <= 0 || p > length children = Nothing
  | otherwise = do
    let (before, child : after) = splitAt (p - 1) children
    child' <- replaceSubterm child (Pos ps) term'
    replaceChildTerms term (before ++ child' : after)
  where
  -- children :: [a]
        children = childTerms term

-- | Replaces all subterms at the given positions with other (type) expressions.
--
--   Returns @Nothing@ if any of the subterms could not be replaced
replaceSubterms :: Subterm a => a -> [(Pos, a)] -> Maybe a
replaceSubterms term []             = return term
replaceSubterms term ((p, e) : pes) = do
  term' <- replaceSubterm term p e
  replaceSubterms term' pes

-------------------------------------------------------------------------------
-- Searching for subterms                                                    --
-------------------------------------------------------------------------------

-- | Gets a list of positions for subterms of the given expression that
--   satisfy the provided predicate.
findSubtermPos :: Subterm a => (a -> Bool) -> a -> [Pos]
findSubtermPos predicate term =
  filter (predicate . fromJust . selectSubterm term) (allPos term)

-- | Gets a list of subterms of the given expression that satisfy the
--   provided predicate.
findSubterms :: Subterm a => (a -> Bool) -> a -> [a]
findSubterms predicate term =
  filter predicate (map (fromJust . selectSubterm term) (allPos term))

-------------------------------------------------------------------------------
-- Bound variables                                                           --
-------------------------------------------------------------------------------

-- | Gets the names of variables that are bound by lambda abstractions or
--   variable patterns in @case@-expressions at the given position of an
--   expression.
--
--   Returns the empty set if the position is invalid.
boundVarsAt :: IR.Expr -> Pos -> Set IR.QName
boundVarsAt = Map.keysSet .: boundVarsWithTypeAt

-- | Like 'boundVarsAt' but also returns the annotated type of then
--   variable pattern.
--
--   Returns an empty map if the position is invalid.
boundVarsWithTypeAt :: IR.Expr -> Pos -> Map IR.QName (Maybe IR.Type)
boundVarsWithTypeAt = fromMaybe Map.empty .: boundVarsWithTypeAt'
 where
  -- | Like 'boundVarsWithTypeAt' but returns @Nothing@ if the given position
  --   is invalid.
  boundVarsWithTypeAt' :: IR.Expr -> Pos -> Maybe (Map IR.QName (Maybe IR.Type))
  boundVarsWithTypeAt' _    (Pos []      ) = return Map.empty
  boundVarsWithTypeAt' expr (Pos (p : ps)) = do
    child <- selectSubterm expr (Pos [p])
    bvars <- boundVarsWithTypeAt' child (Pos ps)
    case expr of
      (IR.Case _ _ alts _) | p > 1 -> do
        let altVars = altBoundVarsWithType (alts !! (p - 2))
        return (bvars `Map.union` altVars)
      (IR.Lambda _ args _ _) -> return (bvars `Map.union` fromVarPats args)
      _                      -> return bvars

  -- | Gets the names of variables bound by the variable patterns of the given
  --   @case@-expression alternative.
  altBoundVarsWithType :: IR.Alt -> Map IR.QName (Maybe IR.Type)
  altBoundVarsWithType (IR.Alt _ _ varPats _) = fromVarPats varPats

  -- | Converts a list of variable patterns to a set of variable names bound
  --   by these patterns.
  fromVarPats :: [IR.VarPat] -> Map IR.QName (Maybe IR.Type)
  fromVarPats = Map.fromList . map (IR.varPatQName &&& IR.varPatType)
