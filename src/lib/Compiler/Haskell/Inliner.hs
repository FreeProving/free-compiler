-- | This module contains functions for inlining the definition of
--   functions into expressions or other function declarations and
--   for expanding type synonyms in type expressions, type signatures
--   as well as data type and other type synonym declarations.
--
--   Inlining is performed during the translation of recursive function
--   declarations to inline the definition of the non-recursive main
--   function into the recursive helper functions.
--
--   The expansion of type synonyms is used to split the type of a function
--   into the types of it's arguments and the return type and during the
--   conversion of mutually recursive data type and type synonym declarations
--   to break the dependency between of the data type declarations on
--   the type synonyms (because they cannot be declared in the same sentence).

module Compiler.Haskell.Inliner where

import           Control.Applicative            ( (<|>) )
import           Control.Monad                  ( when )
import           Control.Monad.Trans.Maybe      ( MaybeT(..) )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromMaybe )

import           Compiler.Environment
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Haskell.Subst
import           Compiler.Haskell.Subterm
import           Compiler.Monad.Class.Hoistable ( hoistMaybe )
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Inlining function declarations                                            --
-------------------------------------------------------------------------------

-- | Inlines the right hand sides of the given function declarations into
--   the right hand sides of other function declarations.
inlineFuncDecls :: [HS.FuncDecl] -> HS.FuncDecl -> Converter HS.FuncDecl
inlineFuncDecls decls decl = do
  let rhs = HS.funcDeclRhs decl
  rhs' <- inlineExpr decls rhs
  return decl { HS.funcDeclRhs = rhs' }

-- | Inlines the right hand sides of the given function declarations into an
--   expression.
inlineExpr :: [HS.FuncDecl] -> HS.Expr -> Converter HS.Expr
inlineExpr decls = inlineAndBind
 where
  -- | Maps the names of function declarations in 'decls' to the arguments
  --   and right hand sides of the functions.
  declMap :: Map HS.QName ([HS.TypeVarDecl], [HS.VarPat], HS.Expr)
  declMap = foldr insertFuncDecl Map.empty decls

  -- | Inserts a function declaration into 'declMap'.
  insertFuncDecl
    :: HS.FuncDecl
    -> Map HS.QName ([HS.TypeVarDecl], [HS.VarPat], HS.Expr)
    -> Map HS.QName ([HS.TypeVarDecl], [HS.VarPat], HS.Expr)
  insertFuncDecl (HS.FuncDecl _ (HS.DeclIdent _ ident) typeArgs args expr _) =
    Map.insert (HS.UnQual (HS.Ident ident)) (typeArgs, args, expr)

  -- | Applies 'inlineExpr'' on the given expression and wraps the result with
  --   lambda abstractions for the remaining arguments.
  --
  --   It is an error if not all type arguments of an inlined function are
  --   bound by visible type application expressions.
  inlineAndBind :: HS.Expr -> Converter HS.Expr
  inlineAndBind expr = do
    (remainingArgs, expr') <- inlineVisiblyApplied expr
    if null remainingArgs
      then return expr'
      else do
        let remainingArgPats = map HS.toVarPat remainingArgs
        return (HS.Lambda NoSrcSpan remainingArgPats expr' Nothing)

  -- | Applies 'inlineExpr'' on the given expression and reports an
  --   internal fatal error if not all type arguments have been
  --   applied visibly.
  inlineVisiblyApplied :: HS.Expr -> Converter ([String], HS.Expr)
  inlineVisiblyApplied e = do
    (remainingTypeArgs, remainingArgs, e') <- inlineExpr' e
    when (not (null remainingTypeArgs))
      $  reportFatal
      $  Message (HS.exprSrcSpan e) Internal
      $  "Missing visible application of "
      ++ show (length remainingTypeArgs)
      ++ " type arguments in an application of '"
      ++ showPretty e
      ++ "'."
    return (remainingArgs, e')

  -- | Performs inlining on the given subexpression.
  --
  --   If a function is inlined, fresh free variables are introduced for the
  --   function arguments. The first two components of the returned tuple
  --   contain the names of the type variables and variables that still need
  --   to be bound. Function application and visible type application
  --   expressions automatically substitute the corresponding argument for
  --   the passed value.
  inlineExpr' :: HS.Expr -> Converter ([String], [String], HS.Expr)
  inlineExpr' var@(HS.Var _ name _) = case Map.lookup name declMap of
    Nothing                    -> return ([], [], var)
    Just (typeArgs, args, rhs) -> do
      (typeArgs', rhs' ) <- renameTypeArgs typeArgs rhs
      (args'    , rhs'') <- renameArgs args rhs'
      return (map HS.fromDeclIdent typeArgs', map HS.varPatIdent args', rhs'')

  -- Substitute argument of inlined function and inline recursively in
  -- function arguments.
  inlineExpr' (HS.App srcSpan e1 e2 exprType) = do
    (remainingArgs, e1') <- inlineVisiblyApplied e1
    e2'                  <- inlineAndBind e2
    case remainingArgs of
      []                     -> return ([], [], HS.App srcSpan e1' e2' exprType)
      (arg : remainingArgs') -> do
        let subst = singleSubst (HS.UnQual (HS.Ident arg)) e2'
        e1'' <- applySubst subst e1'
        return ([], remainingArgs', e1'')

  -- Substitute type arguments of inlined function.
  inlineExpr' (HS.TypeAppExpr srcSpan e t exprType) = do
    (remainingTypeArgs, remainingArgs, e') <- inlineExpr' e
    case remainingTypeArgs of
      [] -> return ([], remainingArgs, HS.TypeAppExpr srcSpan e' t exprType)
      (typeArg : remainingTypeArgs') -> do
        let subst = singleSubst (HS.UnQual (HS.Ident typeArg)) t
        e'' <- applySubst subst e'
        return (remainingTypeArgs', remainingArgs, e'')

  -- Inline recursively.
  inlineExpr' (HS.If srcSpan e1 e2 e3 exprType) = do
    e1' <- inlineAndBind e1
    e2' <- inlineAndBind e2
    e3' <- inlineAndBind e3
    return ([], [], HS.If srcSpan e1' e2' e3' exprType)
  inlineExpr' (HS.Case srcSpan expr alts exprType) = do
    expr' <- inlineAndBind expr
    alts' <- mapM inlineAlt alts
    return ([], [], HS.Case srcSpan expr' alts' exprType)
  inlineExpr' (HS.Lambda srcSpan varPats expr exprType) =
    shadowVarPats varPats $ do
      expr' <- inlineAndBind expr
      return ([], [], HS.Lambda srcSpan varPats expr' exprType)
  inlineExpr' (HS.ExprTypeSig srcSpan expr typeExpr exprType) = do
    expr' <- inlineAndBind expr
    return ([], [], HS.ExprTypeSig srcSpan expr' typeExpr exprType)

  -- All other expressions remain unchanged.
  inlineExpr' expr@(HS.Con _ _ _       ) = return ([], [], expr)
  inlineExpr' expr@(HS.Undefined _ _   ) = return ([], [], expr)
  inlineExpr' expr@(HS.ErrorExpr  _ _ _) = return ([], [], expr)
  inlineExpr' expr@(HS.IntLiteral _ _ _) = return ([], [], expr)

  -- | Performs inlining on the right hand side of the given @case@-expression
  --   alternative.
  inlineAlt :: HS.Alt -> Converter HS.Alt
  inlineAlt (HS.Alt srcSpan conPat varPats expr) = shadowVarPats varPats $ do
    expr' <- inlineAndBind expr
    return (HS.Alt srcSpan conPat varPats expr')

-------------------------------------------------------------------------------
-- Expanding type synonyms                                                   --
-------------------------------------------------------------------------------

-- | Expands all type synonyms in all types in the given data type or type
--   synonym declaration.
expandAllTypeSynonymsInDecl :: HS.TypeDecl -> Converter HS.TypeDecl
expandAllTypeSynonymsInDecl (HS.TypeSynDecl srcSpan declIdent typeVarDecls typeExpr)
  = do
    typeExpr' <- expandAllTypeSynonyms typeExpr
    return (HS.TypeSynDecl srcSpan declIdent typeVarDecls typeExpr')
expandAllTypeSynonymsInDecl (HS.DataDecl srcSpan declIdent typeVarDecls conDecls)
  = do
    conDecls' <- mapM expandAllTypeSynonymsInConDecl conDecls
    return (HS.DataDecl srcSpan declIdent typeVarDecls conDecls')

-- | Expands all type synonyms in all types in the given constructor
--   declaration.
expandAllTypeSynonymsInConDecl :: HS.ConDecl -> Converter HS.ConDecl
expandAllTypeSynonymsInConDecl (HS.ConDecl srcSpan declIdent argTypes) = do
  argTypes' <- mapM expandAllTypeSynonyms argTypes
  return (HS.ConDecl srcSpan declIdent argTypes')

-- | Expands the outermost type synonym in the given type expression.
expandTypeSynonym :: HS.Type -> Converter HS.Type
expandTypeSynonym = expandTypeSynonyms 1

-- | Expands all type synonyms used in the given type expression by the type
--   they are associated with in the current environment.
expandAllTypeSynonyms :: HS.Type -> Converter HS.Type
expandAllTypeSynonyms = expandTypeSynonyms (-1)

-- | Like 'expandAllTypeSynonyms' but accepts an additional argument for the
--   maximum depth.
--
--   If the maximum depth if @0@, the type will be returned unchanged.
--   If it is @1@ only the outermost type synonym will be expanded.
--   If it is negative, all type synonyms will be expanded (see also
--   'expandAllTypeSynonyms').
expandTypeSynonyms :: Int -> HS.Type -> Converter HS.Type
expandTypeSynonyms maxDepth t0
  | maxDepth == 0 = return t0
  | otherwise = do
    t0' <- expandTypeSynonyms' t0 []
    return (fromMaybe t0 t0')
 where
  expandTypeSynonyms' :: HS.Type -> [HS.Type] -> Converter (Maybe HS.Type)
  expandTypeSynonyms' (HS.TypeCon _ typeConName) args = do
    mTypeSynonym <- inEnv $ lookupTypeSynonym typeConName
    case mTypeSynonym of
      Nothing                   -> return Nothing
      Just (typeVars, typeExpr) -> do
        let subst = composeSubsts
              (zipWith (singleSubst . HS.UnQual . HS.Ident) typeVars args)
        typeExpr' <- applySubst subst typeExpr
        Just <$> expandTypeSynonyms (maxDepth - 1) typeExpr'

  expandTypeSynonyms' (HS.TypeApp srcSpan t1 t2) args = do
    t2' <- expandTypeSynonyms (maxDepth - 1) t2
    let args' = t2' : args
    t1' <- expandTypeSynonyms' t1 args'
    return (t1' <|> Just (HS.typeApp srcSpan t1 args'))

  expandTypeSynonyms' (HS.FuncType srcSpan t1 t2) _ = do
    t1' <- expandTypeSynonyms (maxDepth - 1) t1
    t2' <- expandTypeSynonyms (maxDepth - 1) t2
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
