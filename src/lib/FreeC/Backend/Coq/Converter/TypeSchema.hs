-- | This module contains functions for converting between type expressions
--   and type schemas.

module FreeC.Backend.Coq.Converter.TypeSchema
  (
    -- * Instantiating type schemas
    instantiateTypeSchema
  , instantiateTypeSchema'
    -- * Abstracting type expressions
  , abstractTypeSchema
  , abstractTypeSchema'
  )
where

import           Data.Composition               ( (.:) )
import           Data.List                      ( (\\)
                                                , partition
                                                )
import           Data.Maybe                     ( fromJust )

import           FreeC.Environment.Fresh
import           FreeC.IR.SrcSpan
import           FreeC.IR.Subst
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Monad.Converter

-------------------------------------------------------------------------------
-- Instantiating type schemas                                                --
-------------------------------------------------------------------------------

-- | Replaces the type variables in the given type schema by fresh type
--   variables.
instantiateTypeSchema :: HS.TypeSchema -> Converter HS.Type
instantiateTypeSchema = fmap fst . instantiateTypeSchema'

-- | Like 'instantiateTypeSchema' but also returns the fresh type variables,
--   the type schema has been instantiated with.
instantiateTypeSchema' :: HS.TypeSchema -> Converter (HS.Type, [HS.Type])
instantiateTypeSchema' (HS.TypeSchema _ typeArgs typeExpr) = do
  (typeArgs', subst) <- renameTypeArgsSubst typeArgs
  let typeExpr' = applySubst subst typeExpr
      typeVars' = map HS.typeVarDeclToType typeArgs'
  return (typeExpr', typeVars')

-------------------------------------------------------------------------------
-- Abstracting type expressions                                              --
-------------------------------------------------------------------------------

-- | Normalizes the names of type variables in the given type and returns
--   it as a type schema.
--
--   The first argument contains the names of type variables that should be
--   bound by the type schema. Usually these are the type variables that
--   occur in the given type (see 'FreeC.IR.Reference.freeTypeVars').
--
--   Fresh type variables used by the given type are replaced by regular type
--   variables with the prefix 'freshTypeArgPrefix'. All other type variables
--   are not renamed.
abstractTypeSchema :: [HS.QName] -> HS.Type -> HS.TypeSchema
abstractTypeSchema = fst .: abstractTypeSchema'

-- | Like 'abstractTypeSchema' but returns the resulting type schema and the
--   substitution that replaces the abstracted type variables by their name in
--   the type schema.
abstractTypeSchema' :: [HS.QName] -> HS.Type -> (HS.TypeSchema, Subst HS.Type)
abstractTypeSchema' ns t =
  let vs         = map (fromJust . HS.identFromQName) ns
      (ivs, uvs) = partition HS.isInternalIdent vs
      vs'        = uvs ++ take (length ivs) (map makeTypeArg [0 ..] \\ uvs)
      ns'        = map (HS.UnQual . HS.Ident) (uvs ++ ivs)
      ts         = map (HS.TypeVar NoSrcSpan) vs'
      subst      = composeSubsts (zipWith singleSubst ns' ts)
      t'         = applySubst subst t
  in  (HS.TypeSchema NoSrcSpan (map (HS.TypeVarDecl NoSrcSpan) vs') t', subst)
 where
  makeTypeArg :: Int -> HS.TypeVarIdent
  makeTypeArg = (freshTypeArgPrefix ++) . show
