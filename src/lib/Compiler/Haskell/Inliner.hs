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

import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( maybe )

import           Compiler.Environment
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Haskell.Subst
import           Compiler.Monad.Converter

-------------------------------------------------------------------------------
-- Inlining function declarations                                            --
-------------------------------------------------------------------------------

-- | Inlines the right hand sides of the given function declarations into
--   the right hand sides of other function declarations.
inlineFuncDecls :: [HS.FuncDecl] -> HS.FuncDecl -> Converter HS.FuncDecl
inlineFuncDecls decls (HS.FuncDecl srcSpan declIdent args expr) = do
  expr' <- inlineExpr decls expr
  return (HS.FuncDecl srcSpan declIdent args expr')

-- | Inlines the right hand sides of the given function declarations into an
--   expression.
inlineExpr :: [HS.FuncDecl] -> HS.Expr -> Converter HS.Expr
inlineExpr decls = inlineAndBind
 where
  -- | Maps the names of function declarations in 'decls' to the arguments
  --   and right hand sides of the functions.
  declMap :: Map HS.QName ([HS.VarPat], HS.Expr)
  declMap = foldr insertFuncDecl Map.empty decls

  -- | Inserts a function declaration into 'declMap'.
  insertFuncDecl
    :: HS.FuncDecl                        -- ^ The declaration to insert.
    -> Map HS.QName ([HS.VarPat], HS.Expr) -- ^ The map to insert into.
    -> Map HS.QName ([HS.VarPat], HS.Expr)
  insertFuncDecl (HS.FuncDecl _ (HS.DeclIdent _ ident) args expr) =
    Map.insert (HS.UnQual (HS.Ident ident)) (args, expr)

  -- | Applies 'inlineExpr'' on the given expression and wraps the result with
  --   lambda abstractions for the remaining arguments.
  inlineAndBind :: HS.Expr -> Converter HS.Expr
  inlineAndBind expr = do
    (remainingArgIdents, expr') <- inlineExpr' expr
    if null remainingArgIdents
      then return expr'
      else do
        let remainingArgPats = map (HS.VarPat NoSrcSpan) remainingArgIdents
        return (HS.Lambda NoSrcSpan remainingArgPats expr')

  -- | Performs inlining on the given subexpression.
  --
  --   If a function is inlined, fresh free variables are introduced for the
  --   function arguments. The first component of the returned pair contains
  --   the names of the variables that still need to be bound. Function
  --   application expressions automatically substitute the corresponding
  --   argument for the passed value.
  inlineExpr' :: HS.Expr -> Converter ([String], HS.Expr)
  inlineExpr' var@(HS.Var _ name) = case Map.lookup name declMap of
    Nothing          -> return ([], var)
    Just (args, rhs) -> do
      (args', rhs')   <- renameArgs args rhs
      Just returnType <- inEnv $ lookupReturnType ValueScope name
      return
        ( map HS.fromVarPat args'
        , HS.ExprTypeSig NoSrcSpan rhs' (HS.TypeSchema NoSrcSpan [] returnType)
        )

  -- Substitute argument of inlined function and inline recursively in
  -- function arguments.
  inlineExpr' (HS.App srcSpan e1 e2) = do
    (remainingArgs, e1') <- inlineExpr' e1
    e2'                  <- inlineAndBind e2
    case remainingArgs of
      []                     -> return ([], HS.App srcSpan e1' e2')
      (arg : remainingArgs') -> do
        let subst = singleSubst (HS.UnQual (HS.Ident arg)) e2'
        e1'' <- applySubst subst e1'
        return (remainingArgs', e1'')

  -- Inline recursively.
  inlineExpr' (HS.If srcSpan e1 e2 e3) = do
    e1' <- inlineAndBind e1
    e2' <- inlineAndBind e2
    e3' <- inlineAndBind e3
    return ([], HS.If srcSpan e1' e2' e3')
  inlineExpr' (HS.Case srcSpan expr alts) = do
    expr' <- inlineAndBind expr
    alts' <- mapM inlineAlt alts
    return ([], HS.Case srcSpan expr' alts')
  inlineExpr' (HS.Lambda srcSpan args expr) = do
    -- TODO shadow args in expr
    expr' <- inlineAndBind expr
    return ([], HS.Lambda srcSpan args expr')
  inlineExpr' (HS.ExprTypeSig srcSpan expr typeExpr) = do
    expr' <- inlineAndBind expr
    return ([], HS.ExprTypeSig srcSpan expr' typeExpr)

  -- All other expressions remain unchanged.
  inlineExpr' expr@(HS.Con _ _       ) = return ([], expr)
  inlineExpr' expr@(HS.Undefined _   ) = return ([], expr)
  inlineExpr' expr@(HS.ErrorExpr  _ _) = return ([], expr)
  inlineExpr' expr@(HS.IntLiteral _ _) = return ([], expr)

  -- | Performs inlining on the right hand side of the given @case@-expression
  --   alternative.
  inlineAlt :: HS.Alt -> Converter HS.Alt
  inlineAlt (HS.Alt srcSpan conPat varPats expr) = do
    -- TODO shadow varPats in expr
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
    return (maybe t0 id t0')
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
        expandTypeSynonyms (maxDepth - 1) typeExpr' >>= return . Just

  expandTypeSynonyms' (HS.TypeApp srcSpan t1 t2) args = do
    t2' <- expandTypeSynonyms (maxDepth - 1) t2
    t1' <- expandTypeSynonyms' t1 (t2' : args)
    return (Just (maybe (HS.TypeApp srcSpan t1 t2') id t1'))

  expandTypeSynonyms' (HS.TypeFunc srcSpan t1 t2) _ = do
    t1' <- expandTypeSynonyms (maxDepth - 1) t1
    t2' <- expandTypeSynonyms (maxDepth - 1) t2
    return (Just (HS.TypeFunc srcSpan t1' t2'))

  expandTypeSynonyms' (HS.TypeVar _ _) _ = return Nothing
