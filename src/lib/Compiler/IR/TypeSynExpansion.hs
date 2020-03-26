-- | This module contains functions for for expanding type synonyms in type
--   expressions, type signatures as well as data type and other type synonym
--   declarations.
--
--   The expansion of type synonyms is used to split the type of a function
--   into the types of it's arguments and the return type. It is also used
--   during the conversion of mutually recursive data type and type synonym
--   declarations to break the dependency of the data type declarations on
--   the type synonyms (because they cannot be declared in the same sentence
--   in Coq).

module Compiler.IR.TypeSynExpansion where

import           Control.Applicative            ( (<|>) )
import           Control.Monad.Trans.Maybe      ( MaybeT(..) )
import           Data.Maybe                     ( fromMaybe )

import           Compiler.Environment
import qualified Compiler.IR.Syntax            as HS
import           Compiler.IR.Subst
import           Compiler.IR.Subterm
import           Compiler.Monad.Class.Hoistable ( hoistMaybe )
import           Compiler.Monad.Converter

-- | Expands all type synonyms in all types in the given data type or type
--   synonym declaration.
expandAllTypeSynonymsInDecl :: HS.TypeDecl -> Converter HS.TypeDecl
expandAllTypeSynonymsInDecl = expandAllTypeSynonymsInDeclWhere (const True)

-- | Like 'expandAllTypeSynonymsInDecl' but expands only type synonyms whose
--   name matches the given predicate.
expandAllTypeSynonymsInDeclWhere
  :: (HS.QName -> Bool) -> HS.TypeDecl -> Converter HS.TypeDecl
expandAllTypeSynonymsInDeclWhere predicate (HS.TypeSynDecl srcSpan declIdent typeVarDecls typeExpr)
  = do
    typeExpr' <- expandAllTypeSynonymsWhere predicate typeExpr
    return (HS.TypeSynDecl srcSpan declIdent typeVarDecls typeExpr')
expandAllTypeSynonymsInDeclWhere predicate (HS.DataDecl srcSpan declIdent typeVarDecls conDecls)
  = do
    conDecls' <- mapM (expandAllTypeSynonymsInConDeclWhere predicate) conDecls
    return (HS.DataDecl srcSpan declIdent typeVarDecls conDecls')

-- | Expands all type synonyms in all types in the given constructor
--   declaration.
expandAllTypeSynonymsInConDecl :: HS.ConDecl -> Converter HS.ConDecl
expandAllTypeSynonymsInConDecl =
  expandAllTypeSynonymsInConDeclWhere (const True)

-- | Like 'expandAllTypeSynonymsInConDecl' but expands only type synonyms whose
--   name matches the given predicate.
expandAllTypeSynonymsInConDeclWhere
  :: (HS.QName -> Bool) -> HS.ConDecl -> Converter HS.ConDecl
expandAllTypeSynonymsInConDeclWhere predicate (HS.ConDecl srcSpan declIdent argTypes)
  = do
    argTypes' <- mapM (expandAllTypeSynonymsWhere predicate) argTypes
    return (HS.ConDecl srcSpan declIdent argTypes')

-- | Expands the outermost type synonym in the given type expression.
expandTypeSynonym :: HS.Type -> Converter HS.Type
expandTypeSynonym = expandTypeSynonyms 1

-- | Expands all type synonyms used in the given type expression by the type
--   they are associated with in the current environment.
expandAllTypeSynonyms :: HS.Type -> Converter HS.Type
expandAllTypeSynonyms = expandAllTypeSynonymsWhere (const True)

-- | Like 'expandAllTypeSynonyms' but expands only type synonyms whose name
--   matches the given predicate.
expandAllTypeSynonymsWhere :: (HS.QName -> Bool) -> HS.Type -> Converter HS.Type
expandAllTypeSynonymsWhere = expandTypeSynonymsWhere (-1)

-- | Like 'expandAllTypeSynonyms' but accepts an additional argument for the
--   maximum depth.
--
--   If the maximum depth if @0@, the type will be returned unchanged.
--   If it is @1@ only the outermost type synonym will be expanded.
--   If it is negative, all type synonyms will be expanded (see also
--   'expandAllTypeSynonyms').
expandTypeSynonyms :: Int -> HS.Type -> Converter HS.Type
expandTypeSynonyms = flip expandTypeSynonymsWhere (const True)

-- | Like 'expandTypeSynonyms' but expands only type synonyms whose name
--   matches the given predicate.
expandTypeSynonymsWhere
  :: Int -> (HS.QName -> Bool) -> HS.Type -> Converter HS.Type
expandTypeSynonymsWhere maxDepth predicate t0
  | maxDepth == 0 = return t0
  | otherwise = do
    t0' <- expandTypeSynonyms' t0 []
    return (fromMaybe t0 t0')
 where
  expandTypeSynonyms' :: HS.Type -> [HS.Type] -> Converter (Maybe HS.Type)
  expandTypeSynonyms' (HS.TypeCon _ typeConName) args = do
    mTypeSynonym <- inEnv $ lookupTypeSynonym typeConName
    case mTypeSynonym of
      Just (typeVars, typeExpr) | predicate typeConName -> do
        let subst = composeSubsts
              (zipWith (singleSubst . HS.UnQual . HS.Ident) typeVars args)
        typeExpr' <- applySubst subst typeExpr
        Just <$> expandTypeSynonymsWhere (maxDepth - 1) predicate typeExpr'
      _ -> return Nothing

  expandTypeSynonyms' (HS.TypeApp srcSpan t1 t2) args = do
    t2' <- expandTypeSynonymsWhere (maxDepth - 1) predicate t2
    let args' = t2' : args
    t1' <- expandTypeSynonyms' t1 args'
    return (t1' <|> Just (HS.typeApp srcSpan t1 args'))

  expandTypeSynonyms' (HS.FuncType srcSpan t1 t2) _ = do
    t1' <- expandTypeSynonymsWhere (maxDepth - 1) predicate t1
    t2' <- expandTypeSynonymsWhere (maxDepth - 1) predicate t2
    return (Just (HS.FuncType srcSpan t1' t2'))

  expandTypeSynonyms' (HS.TypeVar _ _) _ = return Nothing

-- | Applies 'expandTypeSynonym' to the subterm at the given position.
--
--   If there are type constructor applications in parent positions, the
--   type arguments from the parent positions are used to expand the type
--   synonym as well.
expandTypeSynonymAt :: Pos -> HS.Type -> Converter HS.Type
expandTypeSynonymAt pos typeExpr = do
  case parentPos pos of
    Just pos' | fromMaybe False (isTypeApp <$> selectSubterm typeExpr pos') ->
      expandTypeSynonymAt pos' typeExpr
    _ -> fmap (fromMaybe typeExpr) $ runMaybeT $ do
      subterm  <- hoistMaybe $ selectSubterm typeExpr pos
      subterm' <- lift $ expandTypeSynonym subterm
      hoistMaybe $ replaceSubterm typeExpr pos subterm'
 where
  -- | Tests whether the given type expression is a type constructor
  --   application.
  isTypeApp :: HS.Type -> Bool
  isTypeApp (HS.TypeApp _ _ _) = True
  isTypeApp _                  = False
