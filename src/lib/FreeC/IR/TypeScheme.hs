-- | This module contains functions for converting between type expressions
--   and type schemes.
module FreeC.IR.TypeScheme
  ( -- * Instantiating type schemes
    instantiateTypeScheme
  , instantiateTypeScheme'
    -- * Abstracting type expressions
  , abstractTypeScheme
  , abstractTypeScheme'
  ) where

import           Data.Composition        ( (.:) )
import           Data.List               ( (\\), partition )
import           Data.Maybe              ( fromJust )

import           FreeC.Environment.Fresh
import           FreeC.IR.SrcSpan
import           FreeC.IR.Subst
import qualified FreeC.IR.Syntax         as IR
import           FreeC.Monad.Converter

-------------------------------------------------------------------------------
-- Instantiating type schemes                                                --
-------------------------------------------------------------------------------
-- | Replaces the type variables in the given type scheme by fresh type
--   variables.
instantiateTypeScheme :: IR.TypeScheme -> Converter IR.Type
instantiateTypeScheme = fmap fst . instantiateTypeScheme'

-- | Like 'instantiateTypeScheme' but also returns the fresh type variables,
--   the type scheme has been instantiated with.
instantiateTypeScheme' :: IR.TypeScheme -> Converter ( IR.Type, [ IR.Type ] )
instantiateTypeScheme' (IR.TypeScheme _ typeArgs typeExpr) = do
  ( typeArgs', subst ) <- renameTypeArgsSubst typeArgs
  let typeExpr' = applySubst subst typeExpr
      typeVars' = map IR.typeVarDeclToType typeArgs'
  return ( typeExpr', typeVars' )

-------------------------------------------------------------------------------
-- Abstracting type expressions                                              --
-------------------------------------------------------------------------------
-- | Normalizes the names of type variables in the given type and returns
--   it as a type scheme.
--
--   The first argument contains the names of type variables that should be
--   bound by the type scheme. Usually these are the type variables that
--   occur in the given type (see 'FreeC.IR.Reference.freeTypeVars').
--
--   Fresh type variables used by the given type are replaced by regular type
--   variables with the prefix 'freshTypeArgPrefix'. All other type variables
--   are not renamed.
abstractTypeScheme :: [ IR.QName ] -> IR.Type -> IR.TypeScheme
abstractTypeScheme = fst .: abstractTypeScheme'

-- | Like 'abstractTypeScheme' but returns the resulting type scheme and the
--   substitution that replaces the abstracted type variables by their name in
--   the type scheme.
abstractTypeScheme'
  :: [ IR.QName ] -> IR.Type -> ( IR.TypeScheme, Subst IR.Type )
abstractTypeScheme' ns t
  = let vs           = map (fromJust . IR.identFromQName) ns
        ( ivs, uvs ) = partition IR.isInternalIdent vs
        vs'          = uvs ++ take (length ivs)
          (map makeTypeArg [ 0 .. ] \\ uvs)
        ns'          = map (IR.UnQual . IR.Ident) (uvs ++ ivs)
        ts           = map (IR.TypeVar NoSrcSpan) vs'
        subst        = composeSubsts (zipWith singleSubst ns' ts)
        t'           = applySubst subst t
    in ( IR.TypeScheme NoSrcSpan (map (IR.TypeVarDecl NoSrcSpan) vs') t'
       , subst
       )
 where
   makeTypeArg :: Int -> IR.TypeVarIdent
   makeTypeArg = (freshTypeArgPrefix ++) . show
