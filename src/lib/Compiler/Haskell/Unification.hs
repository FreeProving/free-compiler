-- | This module contains functions for calculating the most general
--   unificator (mgu) for Haskell type expressions.

module Compiler.Haskell.Unification
  ( -- * Error reporting
    UnificationError(..)
  , reportUnificationError
  , unifyOrFail
  , unifyAllOrFail
    -- * Unification
  , unify
  , unifyAll
  )
where

import           Control.Monad.Trans.Except     ( ExceptT
                                                , runExceptT
                                                , throwE
                                                )
import           Data.Composition               ( (.:) )

import           Compiler.Environment.Entry
import           Compiler.Environment.LookupOrFail
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Inliner
import           Compiler.Haskell.SrcSpan
import           Compiler.Haskell.Subst
import           Compiler.Haskell.Subterm
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty                ( showPretty )

-------------------------------------------------------------------------------
-- Error reporting                                                           --
-------------------------------------------------------------------------------

-- | An error that can occur during the unification of two types.
data UnificationError
  = UnificationError HS.Type HS.Type
  | OccursCheckFailure HS.TypeVarIdent HS.Type

-- | Reports the given 'UnificationError'.
reportUnificationError :: MonadReporter m => SrcSpan -> UnificationError -> m a
reportUnificationError srcSpan err = case err of
  UnificationError actualType expectedType -> do
    reportFatal
      $  Message srcSpan Error
      $  "Could not match expected type `"
      ++ showPretty expectedType
      ++ "` with actual type `"
      ++ showPretty actualType
      ++ "`."
  OccursCheckFailure x u ->
    reportFatal
      $  Message srcSpan Error
      $  "Occurs check: Could not construct infinite type `"
      ++ showPretty x
      ++ "` ~ `"
      ++ showPretty u
      ++ "`."

-- | Runs the given converter an reports unification errors using
--   'reportUnificationError'.
runOrFail :: SrcSpan -> ExceptT UnificationError Converter a -> Converter a
runOrFail srcSpan mx =
  runExceptT mx >>= either (reportUnificationError srcSpan) return

-- | Like 'unify' but reports a fatal error message if the types cannot be
--   unified.
--
--   The error message uses the given location information.
unifyOrFail :: SrcSpan -> HS.Type -> HS.Type -> Converter (Subst HS.Type)
unifyOrFail srcSpan = runOrFail srcSpan .: unify

-- | Like 'unifyAll' but reports a fatal error message if the types cannot be
--   unified.
--
--   The error message uses the given location information.
unifyAllOrFail :: SrcSpan -> [HS.Type] -> Converter (Subst HS.Type)
unifyAllOrFail srcSpan = runOrFail srcSpan . unifyAll

-------------------------------------------------------------------------------
-- Unification                                                               --
-------------------------------------------------------------------------------

-- | Calculates the mgu of the given type expressions.
--
--   The algorithm will preferably map the internal variable names to
--   non-internal variables. This ensures that the names specified by
--   the user are preserved. Otherwise variables in the first argument
--   preferably mapped to variables in the second argument.
--
--   Type synonyms are expanded only when necessary.
unify
  :: HS.Type -> HS.Type -> ExceptT UnificationError Converter (Subst HS.Type)
unify t s = do
  ds <- lift $ disagreementSet t s
  case ds of
    Nothing -> return identitySubst
    Just (_, u@(HS.TypeVar _ x), v@(HS.TypeVar _ y))
      | HS.isInternalIdent x -> x `mapsTo` v
      | HS.isInternalIdent y -> y `mapsTo` u
    Just (_  , HS.TypeVar _ x, v             ) -> x `mapsTo` v
    Just (_  , u             , HS.TypeVar _ y) -> y `mapsTo` u
    Just (pos, u             , v             ) -> do
      t' <- lift $ expandTypeSynonymAt pos t
      s' <- lift $ expandTypeSynonymAt pos s
      if t /= t' || s /= s' then unify t' s' else throwE $ UnificationError u v
 where
  -- | Maps the given variable to the given type expression and continues
  --   with the next iteration of the unification algorithm.
  mapsTo
    :: HS.TypeVarIdent
    -> HS.Type
    -> ExceptT UnificationError Converter (Subst HS.Type)
  x `mapsTo` u = do
    occursCheck u
    let subst = singleSubst (HS.UnQual (HS.Ident x)) u
    t'  <- lift $ applySubst subst t
    s'  <- lift $ applySubst subst s
    mgu <- unify t' s'
    return (composeSubst mgu subst)
   where
    -- | Tests whether the type variable occurs in the given type expression.
    --
    --   Reports a fatal error if the variable is found.
    occursCheck :: HS.Type -> ExceptT UnificationError Converter ()
    occursCheck (HS.TypeVar _ y) | x == y    = throwE $ OccursCheckFailure x u
                                 | otherwise = return ()
    occursCheck (HS.TypeCon _ _     ) = return ()
    occursCheck (HS.TypeApp  _ t1 t2) = occursCheck t1 >> occursCheck t2
    occursCheck (HS.TypeFunc _ t1 t2) = occursCheck t1 >> occursCheck t2

-- | Computes the most general unificator for all given type expressions.
unifyAll :: [HS.Type] -> ExceptT UnificationError Converter (Subst HS.Type)
unifyAll []             = return identitySubst
unifyAll [_           ] = return identitySubst
unifyAll (t0 : t1 : ts) = do
  mgu  <- unify t0 t1
  t1'  <- lift $ applySubst mgu t1
  mgu' <- unifyAll (t1' : ts)
  return (composeSubst mgu mgu')

-------------------------------------------------------------------------------
-- Disagreement set                                                          --
-------------------------------------------------------------------------------

-- | Type synonym for a disagreement set.
type DisagreementSet = Maybe (Pos, HS.Type, HS.Type)

-- | Gets subterms at the left-most inner-most position where the
--   two given types differ.
--
--   Returns the subterms and the position of those subterms or @Nothing@
--   if both terms are equal.
disagreementSet :: HS.Type -> HS.Type -> Converter DisagreementSet

-- Two variables disagree if they are not the same variable.
disagreementSet (HS.TypeVar _ x) (HS.TypeVar _ y) | x == y = return Nothing

-- Two constructors disagree if they do not refer to the same environment
-- entries (i.e. the entries have different names).
-- If both constructors have the same name already, we do not have to
-- look them up in the environment first.
disagreementSet t@(HS.TypeCon _ c) s@(HS.TypeCon _ d)
  | c == d = return Nothing
  | otherwise = do
    e <- lookupEntryOrFail (HS.getSrcSpan t) TypeScope c
    f <- lookupEntryOrFail (HS.getSrcSpan t) TypeScope d
    let n = entryName e
        m = entryName f
    if n == m then return Nothing else return (Just (rootPos, t, s))

-- Compute disagreement set recursively.
disagreementSet (HS.TypeApp _ t1 t2) (HS.TypeApp _ s1 s2) =
  disagreementSet' 1 [t1, t2] [s1, s2]
disagreementSet (HS.TypeFunc _ t1 t2) (HS.TypeFunc _ s1 s2) =
  disagreementSet' 1 [t1, t2] [s1, s2]

-- If the two types have a different constructor, they disagree.
disagreementSet t s = return (Just (rootPos, t, s))

-- | Computes the disagreement sets for each pair of the given types and
--   returns the first non-empty disagreement set extended by it's position
--   in the list.
--
--   The first parameter is the child position of the first element in the
--   list.
disagreementSet' :: Int -> [HS.Type] -> [HS.Type] -> Converter DisagreementSet
disagreementSet' i (t : ts) (s : ss) = do
  ds <- disagreementSet t s
  case ds of
    Nothing            -> disagreementSet' (i + 1) ts ss
    Just (pos, t', s') -> return (Just (consPos i pos, t', s'))
disagreementSet' _ _ _ = return Nothing
