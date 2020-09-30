-- | This module contains data types and functions for working with subterms
--   of expressions and type expressions.
--
--   There are also functions for finding the names and types of variables that
--   are bound at a given position in an expression.
module FreeC.IR.Subterm
  ( -- * Direct Children
    childTerms
  , replaceChildTerms
    -- * Positions
  , Pos(..)
  , rootPos
  , consPos
  , unConsPos
  , parentPos
  , ancestorPos
  , allPos
  , above
  , below
  , leftOf
  , rightOf
    -- * Subterms
  , selectSubterm
  , selectSubterm'
  , replaceSubterm
  , replaceSubterm'
  , replaceSubterms
  , replaceSubterms'
    -- * Searching for Subterms
  , findSubtermPos
  , findSubtermWithPos
  , findSubterms
  , findFirstSubterm
    -- * Replacing Subterms
  , mapSubterms
  , mapSubtermsM
    -- * Bound Variables
  , boundVarsOf
  , boundVarsWithTypeOf
  , boundVarsAt
  , boundVarsWithTypeAt
  ) where

import           Control.Monad         ( foldM )
import           Data.Composition      ( (.:) )
import           Data.Functor.Identity ( runIdentity )
import           Data.List             ( inits, intersperse, isPrefixOf )
import           Data.Map.Strict       ( Map )
import qualified Data.Map.Strict       as Map
import           Data.Maybe            ( fromMaybe, listToMaybe )
import           Data.Set              ( Set )
import           Data.Tuple.Extra      ( (&&&) )

import qualified FreeC.IR.Syntax       as IR
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Utility Functions                                                         --
-------------------------------------------------------------------------------
-- | Runs the given function on the given list if the latter has the specified
--   number of arguments.
--
--   Returns the function's result of @Nothing@ if the list has the wrong
--   number of elements.
checkArity :: Int -> ([a] -> b) -> [a] -> Maybe b
checkArity n f xs | length xs == n = Just (f xs)
                  | otherwise = Nothing

-- | Like 'checkArity' for functions that do no expect any arguments.
nullary :: b -> [a] -> Maybe b
nullary y xs | null xs = Just y
             | otherwise = Nothing

-- | Throws an error that the subterm of the given term of the given position
--   does not exists.
--
--   The error message is annotated with the given function name.
missingPosError :: Subterm a => String -> a -> Pos -> a
missingPosError funcName term pos = error
  $ funcName
  ++ ": The subterm at position "
  ++ showPretty pos
  ++ "in term "
  ++ showPretty term
  ++ " does not exists."

-------------------------------------------------------------------------------
-- Direct Children                                                           --
-------------------------------------------------------------------------------
-- | Type class for AST nodes with child nodes of the same type.
--
--   It is a subclass of 'Pretty' so error messages involving subterms can be
--   pretty printed.
class Pretty a => Subterm a where
  -- | Gets the child nodes of the given AST node.
  childTerms :: a -> [a]

  -- | Replaces the child nodes of the given AST node.
  replaceChildTerms :: a -> [a] -> Maybe a

-- | Like 'replaceChildTerms' but throws an error if the wrong number of child
--   terms is provided.
replaceChildTerms' :: Subterm a => a -> [a] -> a
replaceChildTerms' term children' = fromMaybe argCountError
  (replaceChildTerms term children')
 where
  -- | The error to throw when the wrong number of new child terms is provided.
  argCountError = error
    $ "replaceChildTerms: Wrong number of child terms. Got "
    ++ show (length children')
    ++ " but expected "
    ++ show (length (childTerms term))
    ++ "!"

-- | Expressions have subterms.
instance Subterm IR.Expr where
  -- | Gets the direct child expression nodes of the given expression.
  childTerms (IR.App _ e1 e2 _)          = [e1, e2]
  childTerms (IR.TypeAppExpr _ expr _ _) = [expr]
  childTerms (IR.If _ e1 e2 e3 _)        = [e1, e2, e3]
  childTerms (IR.Case _ expr alts _)     = expr : map IR.altRhs alts
  childTerms (IR.Lambda _ _ expr _)      = [expr]
  childTerms (IR.Con _ _ _)              = []
  childTerms (IR.Var _ _ _)              = []
  childTerms (IR.Undefined _ _)          = []
  childTerms (IR.ErrorExpr _ _ _)        = []
  childTerms (IR.IntLiteral _ _ _)       = []
  childTerms (IR.Let _ binds e _)        = e : map IR.bindExpr binds

  -- | Replaces all direct child expression nodes of the given expression.
  replaceChildTerms (IR.App srcSpan _ _ exprType)
    = checkArity 2 $ \[e1', e2'] -> IR.App srcSpan e1' e2' exprType
  replaceChildTerms (IR.TypeAppExpr srcSpan _ typeExpr exprType)
    = checkArity 1 $ \[expr'] -> IR.TypeAppExpr srcSpan expr' typeExpr exprType
  replaceChildTerms (IR.If srcSpan _ _ _ exprType)
    = checkArity 3 $ \[e1', e2', e3'] -> IR.If srcSpan e1' e2' e3' exprType
  replaceChildTerms (IR.Case srcSpan _ alts exprType)
    = checkArity (length alts + 1) $ \(expr' : altChildren') -> IR.Case srcSpan
    expr' (zipWith replaceAltChildExpr alts altChildren') exprType
   where
    -- | Replaces the expression on the right-hand side of the given
    --   @case@-expression alternative.
    replaceAltChildExpr :: IR.Alt -> IR.Expr -> IR.Alt
    replaceAltChildExpr alt rhs' = alt { IR.altRhs = rhs' }
  replaceChildTerms (IR.Lambda srcSpan args _ exprType)
    = checkArity 1 $ \[expr'] -> IR.Lambda srcSpan args expr' exprType
  replaceChildTerms (IR.Let srcSpan binds _ exprType)
    = checkArity (length binds + 1) $ \(expr' : bindChildren') -> IR.Let srcSpan
    (zipWith replaceBindChildExpr binds bindChildren') expr' exprType
   where
    -- | Replaces the expression on the right hand side of the given
    --   @let@-expression bindings.
    replaceBindChildExpr :: IR.Bind -> IR.Expr -> IR.Bind
    replaceBindChildExpr b expr = b { IR.bindExpr = expr }
  replaceChildTerms expr@(IR.Con _ _ _) = nullary expr
  replaceChildTerms expr@(IR.Var _ _ _) = nullary expr
  replaceChildTerms expr@(IR.Undefined _ _) = nullary expr
  replaceChildTerms expr@(IR.ErrorExpr _ _ _) = nullary expr
  replaceChildTerms expr@(IR.IntLiteral _ _ _) = nullary expr

-- | Type expressions have subterms.
instance Subterm IR.Type where
  -- | Gets the direct child type expression nodes of the given type
  --   expression.
  childTerms (IR.TypeVar _ _)      = []
  childTerms (IR.TypeCon _ _)      = []
  childTerms (IR.TypeApp _ t1 t2)  = [t1, t2]
  childTerms (IR.FuncType _ t1 t2) = [t1, t2]

  -- | Replaces all direct child type expression nodes of the given type
  --   expression.
  replaceChildTerms typeExpr@(IR.TypeVar _ _) = nullary typeExpr
  replaceChildTerms typeExpr@(IR.TypeCon _ _) = nullary typeExpr
  replaceChildTerms (IR.TypeApp srcSpan _ _)
    = checkArity 2 $ \[t1', t2'] -> IR.TypeApp srcSpan t1' t2'
  replaceChildTerms (IR.FuncType srcSpan _ _)
    = checkArity 2 $ \[t1', t2'] -> IR.FuncType srcSpan t1' t2'

-------------------------------------------------------------------------------
-- Positions                                                                 --
-------------------------------------------------------------------------------
-- | Describes a position of a subterm within a Haskell expression.
newtype Pos = Pos [Int]
 deriving ( Eq, Show )

-- | Pretty prints a position.
instance Pretty Pos where
  pretty (Pos xs)
    = char '<' <> hcat (intersperse (char '.') (map int xs)) <> char '>'

-- | Position of the root expression.
rootPos :: Pos
rootPos = Pos []

-- | Extends a position inside of a child node to a position inside of a
--   parent node.
--
--   If @pos@ is the position of a subterm @s@ of an expression or
--   type expression @tᵢ@, then @consPos i pos@ is the position of
--   the subterm @s@ of a term @C t₁ ... tᵢ ... tₙ@.
consPos :: Int -> Pos -> Pos
consPos p (Pos ps) = Pos (p : ps)

-- | Inverse function of 'consPos'.
--
--   Returns @Nothing@ if the given position is the 'rootPos'.
unConsPos :: Pos -> Maybe (Int, Pos)
unConsPos (Pos [])       = Nothing
unConsPos (Pos (p : ps)) = Just (p, Pos ps)

-- | Gets the parent position or @Nothing@ if the given position is the
--   root position.
parentPos :: Pos -> Maybe Pos
parentPos (Pos ps) | null ps = Nothing
                   | otherwise = Just (Pos (init ps))

-- | Gets the positions of all ancestors of the the given position including
--   the position itself.
ancestorPos :: Pos -> [Pos]
ancestorPos (Pos ps) = map Pos (inits ps)

-- | Gets all valid positions of subterms within the given Haskell expression.
allPos :: Subterm a => a -> [Pos]
allPos term = rootPos
  : [consPos p childPos
    | (p, child) <- zip [1 ..] (childTerms term)
    , childPos <- allPos child
    ]

-- | Tests whether a position is above another one.
above :: Pos -> Pos -> Bool
above (Pos ps1) (Pos ps2) = ps1 `isPrefixOf` ps2

-- | Tests whether a position is below another one.
below :: Pos -> Pos -> Bool
below = flip above

-- | Tests whether a position is left of another one.
leftOf :: Pos -> Pos -> Bool
leftOf (Pos []) _ = False
leftOf _ (Pos []) = False
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
  | otherwise = selectSubterm (children !! (p - 1)) (Pos ps)
 where
  {- children :: [a] -}
  children = childTerms term

-- | Like 'selectSubterm' but throws an error if there is no such subterm.
selectSubterm' :: Subterm a => a -> Pos -> a
selectSubterm' term pos = fromMaybe (missingPosError "selectSubterm" term pos)
  (selectSubterm term pos)

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
  {- children :: [a] -}
  children = childTerms term

-- | Like 'replaceSubterm' but throws an error if there is no such subterm.
replaceSubterm' :: Subterm a => a -> Pos -> a -> a
replaceSubterm' term pos term' = fromMaybe
  (missingPosError "replaceSubterm" term pos) (replaceSubterm term pos term')

-- | Replaces all subterms at the given positions with other (type) expressions.
--
--   Returns @Nothing@ if any of the subterms could not be replaced
replaceSubterms :: Subterm a => a -> [(Pos, a)] -> Maybe a
replaceSubterms = foldM (\term (pos, term') -> replaceSubterm term pos term')

-- | Like 'replaceSubterms' but throws an error if any of the subterms could
--   not be replaced.
replaceSubterms' :: Subterm a => a -> [(Pos, a)] -> a
replaceSubterms' = foldl (\term (pos, term') -> replaceSubterm' term pos term')

-------------------------------------------------------------------------------
-- Searching for Subterms                                                    --
-------------------------------------------------------------------------------
-- | Gets a list of positions for subterms of the given expression that
--   satisfy the provided predicate.
findSubtermPos :: Subterm a => (a -> Bool) -> a -> [Pos]
findSubtermPos predicate = map snd
  . findSubtermWithPos (flip (const predicate))

-- | Like 'findSubtermPos' but the predicate gets the position as an additional
--   argument and also returns the subterm.
findSubtermWithPos :: Subterm a => (a -> Pos -> Bool) -> a -> [(a, Pos)]
findSubtermWithPos predicate term = filter (uncurry predicate)
  (map (selectSubterm' term &&& id) (allPos term))

-- | Gets a list of subterms of the given expression that satisfy the
--   provided predicate.
findSubterms :: Subterm a => (a -> Bool) -> a -> [a]
findSubterms predicate = map fst . findSubtermWithPos (flip (const predicate))

-- | Gets the first subterm of the given expression that satisfies the
--   provided predicate.
--
--   Return @Nothing@ if there is no such subterm.
findFirstSubterm :: Subterm a => (a -> Bool) -> a -> Maybe a
findFirstSubterm = listToMaybe .: findSubterms

-------------------------------------------------------------------------------
-- Replacing for Subterms                                                    --
-------------------------------------------------------------------------------
-- | Applies the given function to all subterms of the given node.
--
--   The subterms of the returned expression are replaced recursively.
mapSubterms :: Subterm a => (a -> a) -> a -> a
mapSubterms f = runIdentity . mapSubtermsM (return . f)

-- Monadic version of 'mapSubterms'.
mapSubtermsM :: (Subterm a, Monad m) => (a -> m a) -> a -> m a
mapSubtermsM f term = do
  term' <- f term
  children' <- mapM (mapSubtermsM f) (childTerms term')
  return (replaceChildTerms' term' children')

-------------------------------------------------------------------------------
-- Bound Variables                                                           --
-------------------------------------------------------------------------------
-- | Gets the names of variables that are bound by the given expression in its
--   subterm at the given index.
--
--   For example, a @case@-expression
--
--   > case e { … ; Cᵢ x₁ … xₙ -> eᵢ ; … }
--
--   with subterms @[e, e₁, …, eₙ]@ binds the variables @x₁ … xₙ@ in it's
--   @i+1@th subterm @eᵢ@ but no variables are bound in @e@ (i.e., if @i = 0@).
--
--   Returns an empty map if the expression does not have such a subterm.
boundVarsOf :: IR.Expr -> Int -> Set IR.QName
boundVarsOf = Map.keysSet .: boundVarsWithTypeOf

-- | Like 'boundVarsOf' but also returns the annotated type of the
--   variable pattern.
--
--   Returns an empty map if the expression does not have such a subterm.
boundVarsWithTypeOf :: IR.Expr -> Int -> Map IR.QName (Maybe IR.Type)
boundVarsWithTypeOf expr i = case expr of
  -- A lambda abstraction binds the arguments in the right-hand side.
  IR.Lambda _ args _ _   -> fromVarPats args
  -- A @let@-expression binds local variables in the @in@-expression
  -- as well as all binders.
  IR.Let _ binds _ _     -> fromVarPats (map IR.bindVarPat binds)
  -- Only alternatives of @case@-expressions bind variables.
  -- The @case@-expression itself does not bind any variables.
  IR.Case _ _ alts _     | i >= 1 && i <= length alts -> fromVarPats
                           (IR.altVarPats (alts !! (i - 1)))
                         | otherwise -> Map.empty
  -- All other expressions don't bind variables.
  IR.Con _ _ _           -> Map.empty
  IR.Var _ _ _           -> Map.empty
  IR.App _ _ _ _         -> Map.empty
  IR.TypeAppExpr _ _ _ _ -> Map.empty
  IR.If _ _ _ _ _        -> Map.empty
  IR.Undefined _ _       -> Map.empty
  IR.ErrorExpr _ _ _     -> Map.empty
  IR.IntLiteral _ _ _    -> Map.empty
 where
  -- | Converts a list of variable patterns to a map from variable names bound
  --   by these patterns to the types they have been annotated with.
  fromVarPats :: [IR.VarPat] -> Map IR.QName (Maybe IR.Type)
  fromVarPats = Map.fromList . map (IR.varPatQName &&& IR.varPatType)

-- | Gets the names of variables that are bound by lambda abstractions or
--   variable patterns in @case@-expressions at the given position of an
--   expression.
--
--   Returns the empty set if the position is invalid.
boundVarsAt :: IR.Expr -> Pos -> Set IR.QName
boundVarsAt = Map.keysSet .: boundVarsWithTypeAt

-- | Like 'boundVarsAt' but also returns the annotated type of the
--   variable pattern.
--
--   Returns an empty map if the position is invalid.
boundVarsWithTypeAt :: IR.Expr -> Pos -> Map IR.QName (Maybe IR.Type)
boundVarsWithTypeAt = fromMaybe Map.empty .: boundVarsWithTypeAt'
 where
  -- | Like 'boundVarsWithTypeAt' but returns @Nothing@ if the given position
  --   is invalid.
  boundVarsWithTypeAt'
    :: IR.Expr -> Pos -> Maybe (Map IR.QName (Maybe IR.Type))
  boundVarsWithTypeAt' _ (Pos [])          = return Map.empty
  boundVarsWithTypeAt' expr (Pos (p : ps)) = do
    child <- selectSubterm expr (Pos [p])
    boundInChild <- boundVarsWithTypeAt' child (Pos ps)
    let boundLocally = boundVarsWithTypeOf expr (p - 1)
    return (boundInChild `Map.union` boundLocally)
