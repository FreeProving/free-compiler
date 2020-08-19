-- | This module contains functions for expanding type synonyms in type
--   expressions, type signatures as well as data type and other type synonym
--   declarations.
--
--   The expansion of type synonyms is used to split the type of a function
--   into the types of its arguments and the return type. It is also used
--   during the conversion of mutually recursive data type and type synonym
--   declarations to break the dependency of the data type declarations on
--   the type synonyms (because they cannot be declared in the same sentence
--   in Coq).
module FreeC.IR.TypeSynExpansion
  ( -- * Type Declarations
    expandAllTypeSynonymsInDecl
  , expandAllTypeSynonymsInDeclWhere
     -- * Constructor Declarations
  , expandAllTypeSynonymsInConDecl
  , expandAllTypeSynonymsInConDeclWhere
     -- * Type Expressions
  , expandTypeSynonym
  , expandAllTypeSynonyms
  , expandAllTypeSynonymsWhere
  , expandTypeSynonyms
  , expandTypeSynonymsWhere
     -- * Subterms of Type Expressions
  , expandTypeSynonymAt
  ) where

import           Control.Applicative         ( (<|>) )
import           Control.Monad.Trans.Maybe   ( MaybeT(..) )
import           Data.Maybe                  ( fromMaybe )

import           FreeC.Environment
import           FreeC.IR.Subst
import           FreeC.IR.Subterm
import qualified FreeC.IR.Syntax             as IR
import           FreeC.Monad.Class.Hoistable ( hoistMaybe )
import           FreeC.Monad.Converter

-------------------------------------------------------------------------------
-- Type Declarations                                                         --
-------------------------------------------------------------------------------
-- | Expands all type synonyms in all types in the given data type or type
--   synonym declaration.
expandAllTypeSynonymsInDecl :: IR.TypeDecl -> Converter IR.TypeDecl
expandAllTypeSynonymsInDecl = expandAllTypeSynonymsInDeclWhere (const True)

-- | Like 'expandAllTypeSynonymsInDecl' but expands only type synonyms whose
--   name matches the given predicate.
expandAllTypeSynonymsInDeclWhere
  :: (IR.QName -> Bool) -> IR.TypeDecl -> Converter IR.TypeDecl
expandAllTypeSynonymsInDeclWhere predicate
  (IR.TypeSynDecl srcSpan declIdent typeVarDecls typeExpr) = do
    typeExpr' <- expandAllTypeSynonymsWhere predicate typeExpr
    return (IR.TypeSynDecl srcSpan declIdent typeVarDecls typeExpr')
expandAllTypeSynonymsInDeclWhere predicate
  (IR.DataDecl srcSpan declIdent typeVarDecls conDecls) = do
    conDecls' <- mapM (expandAllTypeSynonymsInConDeclWhere predicate) conDecls
    return (IR.DataDecl srcSpan declIdent typeVarDecls conDecls')

-------------------------------------------------------------------------------
-- Constructor Declarations                                                  --
-------------------------------------------------------------------------------
-- | Expands all type synonyms in all types in the given constructor
--   declaration.
expandAllTypeSynonymsInConDecl :: IR.ConDecl -> Converter IR.ConDecl
expandAllTypeSynonymsInConDecl = expandAllTypeSynonymsInConDeclWhere
  (const True)

-- | Like 'expandAllTypeSynonymsInConDecl' but expands only type synonyms whose
--   name matches the given predicate.
expandAllTypeSynonymsInConDeclWhere
  :: (IR.QName -> Bool) -> IR.ConDecl -> Converter IR.ConDecl
expandAllTypeSynonymsInConDeclWhere predicate
  (IR.ConDecl srcSpan declIdent argTypes) = do
    argTypes' <- mapM (expandAllTypeSynonymsWhere predicate) argTypes
    return (IR.ConDecl srcSpan declIdent argTypes')

-------------------------------------------------------------------------------
-- Type Expressions                                                          --
-------------------------------------------------------------------------------
-- | Expands the outermost type synonym in the given type expression.
expandTypeSynonym :: IR.Type -> Converter IR.Type
expandTypeSynonym = expandTypeSynonyms 1

-- | Expands all type synonyms used in the given type expression by the type
--   they are associated with in the current environment.
expandAllTypeSynonyms :: IR.Type -> Converter IR.Type
expandAllTypeSynonyms = expandAllTypeSynonymsWhere (const True)

-- | Like 'expandAllTypeSynonyms' but expands only type synonyms whose name
--   matches the given predicate.
expandAllTypeSynonymsWhere
  :: (IR.QName -> Bool) -> IR.Type -> Converter IR.Type
expandAllTypeSynonymsWhere = expandTypeSynonymsWhere (-1)

-- | Like 'expandAllTypeSynonyms' but accepts an additional argument for the
--   maximum depth.
--
--   If the maximum depth is @0@, the type will be returned unchanged.
--   If it is @1@, only the outermost type synonym will be expanded.
--   If it is negative, all type synonyms will be expanded (see also
--   'expandAllTypeSynonyms').
expandTypeSynonyms :: Int -> IR.Type -> Converter IR.Type
expandTypeSynonyms = flip expandTypeSynonymsWhere (const True)

-- | Like 'expandTypeSynonyms' but expands only type synonyms whose name
--   matches the given predicate.
expandTypeSynonymsWhere
  :: Int -> (IR.QName -> Bool) -> IR.Type -> Converter IR.Type
expandTypeSynonymsWhere maxDepth predicate t0
  | maxDepth == 0 = return t0
  | otherwise = do
    t0' <- expandTypeSynonyms' t0 []
    return (fromMaybe t0 t0')
 where
  expandTypeSynonyms' :: IR.Type -> [IR.Type] -> Converter (Maybe IR.Type)
  expandTypeSynonyms' (IR.TypeCon _ typeConName) args = do
    mTypeSynonym <- inEnv $ lookupTypeSynonym typeConName
    case mTypeSynonym of
      Just (typeVars, typeExpr)
        | predicate typeConName -> do
          let subst     = composeSubsts
                (zipWith (singleSubst . IR.UnQual . IR.Ident) typeVars args)
              typeExpr' = applySubst subst typeExpr
          Just <$> expandTypeSynonymsWhere (maxDepth - 1) predicate typeExpr'
      _ -> return Nothing
  expandTypeSynonyms' (IR.TypeApp srcSpan t1 t2) args = do
    t2' <- expandTypeSynonymsWhere (maxDepth - 1) predicate t2
    let args' = t2' : args
    t1' <- expandTypeSynonyms' t1 args'
    return (t1' <|> Just (IR.typeApp srcSpan t1 args'))
  expandTypeSynonyms' (IR.FuncType srcSpan t1 t2) _   = do
    t1' <- expandTypeSynonymsWhere (maxDepth - 1) predicate t1
    t2' <- expandTypeSynonymsWhere (maxDepth - 1) predicate t2
    return (Just (IR.FuncType srcSpan t1' t2'))
  expandTypeSynonyms' (IR.TypeVar _ _) _              = return Nothing

-------------------------------------------------------------------------------
-- Subterms of Type Expressions                                              --
-------------------------------------------------------------------------------
-- | Applies 'expandTypeSynonym' to the subterm at the given position.
--
--   If there are type constructor applications in parent positions, the
--   type arguments from the parent positions are used to expand the type
--   synonym as well.
expandTypeSynonymAt :: Pos -> IR.Type -> Converter IR.Type
expandTypeSynonymAt pos typeExpr = case parentPos pos of
  Just pos' | maybe False isTypeApp (selectSubterm typeExpr pos') ->
              expandTypeSynonymAt pos' typeExpr
  _         -> fmap (fromMaybe typeExpr) $ runMaybeT $ do
    subterm <- hoistMaybe $ selectSubterm typeExpr pos
    subterm' <- lift $ expandTypeSynonym subterm
    hoistMaybe $ replaceSubterm typeExpr pos subterm'
 where
  -- | Tests whether the given type expression is a type constructor
  --   application.
  isTypeApp :: IR.Type -> Bool
  isTypeApp (IR.TypeApp _ _ _) = True
  isTypeApp _ = False
