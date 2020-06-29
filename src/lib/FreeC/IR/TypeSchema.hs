-- | This module contains functions for converting between type expressions
--   and type schemas.

module FreeC.IR.TypeSchema
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
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter

-------------------------------------------------------------------------------
-- Instantiating type schemas                                                --
-------------------------------------------------------------------------------

-- | Replaces the type variables in the given type schema by fresh type
--   variables.
instantiateTypeSchema :: IR.TypeSchema -> Converter IR.Type
instantiateTypeSchema = fmap fst . instantiateTypeSchema'

-- | Like 'instantiateTypeSchema' but also returns the fresh type variables
--   the type schema has been instantiated with.
instantiateTypeSchema' :: IR.TypeSchema -> Converter (IR.Type, [IR.Type])
instantiateTypeSchema' (IR.TypeSchema _ typeArgs typeExpr) = do
  (typeArgs', subst) <- renameTypeArgsSubst typeArgs
  let typeExpr' = applySubst subst typeExpr
      typeVars' = map IR.typeVarDeclToType typeArgs'
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
abstractTypeSchema :: [IR.QName] -> IR.Type -> IR.TypeSchema
abstractTypeSchema = fst .: abstractTypeSchema'

-- | Like 'abstractTypeSchema' but returns the resulting type schema and the
--   substitution that replaces the abstracted type variables by their name in
--   the type schema.
abstractTypeSchema' :: [IR.QName] -> IR.Type -> (IR.TypeSchema, Subst IR.Type)
abstractTypeSchema' ns t =
  let vs         = map (fromJust . IR.identFromQName) ns
      (ivs, uvs) = partition IR.isInternalIdent vs
      vs'        = uvs ++ take (length ivs) (map makeTypeArg [0 ..] \\ uvs)
      ns'        = map (IR.UnQual . IR.Ident) (uvs ++ ivs)
      ts         = map (IR.TypeVar NoSrcSpan) vs'
      subst      = composeSubsts (zipWith singleSubst ns' ts)
      t'         = applySubst subst t
  in  (IR.TypeSchema NoSrcSpan (map (IR.TypeVarDecl NoSrcSpan) vs') t', subst)
 where
  makeTypeArg :: Int -> IR.TypeVarIdent
  makeTypeArg = (freshTypeArgPrefix ++) . show
