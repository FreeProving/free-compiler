-- | This module contains functions for calculating the most general
--   unificator (mgu) for Haskell type expressions.

module Compiler.Haskell.Unification
  ( unify
  , unifyAll
  )
where

import           Control.Applicative            ( empty
                                                , (<|>)
                                                )

import           Compiler.Environment.Resolver
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Inliner
import           Compiler.Haskell.Subst
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty                ( showPretty )

-- | Calculates the mgu of the given type expressions.
--
--   The algorithm will preferably map the internal variable names to
--   non-internal variables. This ensures that the names specified by
--   the user are preserved. Otherwise variables in the first argument
--   preferably mapped to variables in the second argument.
--
--   Reports a fatal error if the types cannot be unified.
unify :: HS.Type -> HS.Type -> Converter (Subst HS.Type)
unify t s = do
  t' <- expandAllTypeSynonyms t >>= resolveTypes
  s' <- expandAllTypeSynonyms s >>= resolveTypes
  unify' t' s'

-- | Like 'compareAndUnify' but assumes the type constructor names to be
--   normalized.
unify' :: HS.Type -> HS.Type -> Converter (Subst HS.Type)
unify' t s = case disagreementSet t s of
  Nothing -> return identitySubst
  Just (u@(HS.TypeVar _ x), v@(HS.TypeVar _ y))
    | HS.isInternalIdent x -> step x v
    | HS.isInternalIdent y -> step y u
  Just (HS.TypeVar _ x, v             ) -> step x v
  Just (u             , HS.TypeVar _ y) -> step y u
  Just (u, v) ->
    reportFatal
      $  Message (HS.getSrcSpan u) Error
      $  "Could not match "
      ++ showPretty u
      ++ " with "
      ++ showPretty v
      ++ " in unification of "
      ++ showPretty t
      ++ " with "
      ++ showPretty s
 where
  -- | Maps the given variable to the given type expression and continues
  --   with the next iteration of the unification algorithm.
  step :: HS.TypeVarIdent -> HS.Type -> Converter (Subst HS.Type)
  step x u = do
    occursCheck x u
    let subst = singleSubst (HS.UnQual (HS.Ident x)) u
    t'  <- applySubst subst t
    s'  <- applySubst subst s
    mgu <- unify' t' s'
    return (composeSubst mgu subst)

  -- | Tests whether the given variable occurs in the given type expression.
  --
  --   Reports a fatal error if the variable is found.
  occursCheck :: HS.TypeVarIdent -> HS.Type -> Converter ()
  occursCheck x (HS.TypeVar srcSpan y)
    | x == y
    = reportFatal
      $  Message srcSpan Error
      $  "Occurs check: Could not unify "
      ++ showPretty t
      ++ " with "
      ++ showPretty s
    | otherwise
    = return ()
  occursCheck _ (HS.TypeCon _ _     ) = return ()
  occursCheck x (HS.TypeApp  _ t1 t2) = occursCheck x t1 >> occursCheck x t2
  occursCheck x (HS.TypeFunc _ t1 t2) = occursCheck x t1 >> occursCheck x t2

-- | Computes the most general unificator for all given type expressions.
unifyAll :: [HS.Type] -> Converter (Subst HS.Type)
unifyAll []             = return identitySubst
unifyAll [_           ] = return identitySubst
unifyAll (t0 : t1 : ts) = do
  mgu  <- unify t0 t1
  t1'  <- applySubst mgu t1
  mgu' <- unifyAll (t1' : ts)
  return (composeSubst mgu mgu')

-- | Gets subterms at the left-most inner-most position where the
--   two gieven types differ.
disagreementSet :: HS.Type -> HS.Type -> Maybe (HS.Type, HS.Type)
disagreementSet (HS.TypeVar _ x) (HS.TypeVar _ y) | x == y = empty
disagreementSet (HS.TypeCon _ c) (HS.TypeCon _ d) | c == d = empty
disagreementSet (HS.TypeApp _ t1 t2) (HS.TypeApp _ s1 s2) =
  disagreementSet t1 s1 <|> disagreementSet t2 s2
disagreementSet (HS.TypeFunc _ t1 t2) (HS.TypeFunc _ s1 s2) =
  disagreementSet t1 s1 <|> disagreementSet t2 s2
disagreementSet t s = return (t, s)
