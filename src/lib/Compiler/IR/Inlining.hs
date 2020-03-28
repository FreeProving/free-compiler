-- | This module contains functions for inlining the definition of
--   functions into expressions or other function declarations.
--
--   Inlining is performed during the translation of recursive function
--   declarations to inline the definition of the non-recursive main
--   function into the recursive helper functions.

module Compiler.IR.Inlining where

import           Control.Monad                  ( when )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map

import           Compiler.IR.SrcSpan
import           Compiler.IR.Subst
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

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
  insertFuncDecl funcDecl = Map.insert
    (HS.funcDeclQName funcDecl)
    ( HS.funcDeclTypeArgs funcDecl
    , HS.funcDeclArgs funcDecl
    , HS.funcDeclRhs funcDecl
    )

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
      return
        (map HS.typeVarDeclIdent typeArgs', map HS.varPatIdent args', rhs'')

  -- Substitute argument of inlined function and inline recursively in
  -- function arguments.
  inlineExpr' (HS.App srcSpan e1 e2 exprType) = do
    (remainingArgs, e1') <- inlineVisiblyApplied e1
    e2'                  <- inlineAndBind e2
    case remainingArgs of
      []                     -> return ([], [], HS.App srcSpan e1' e2' exprType)
      (arg : remainingArgs') -> do
        let subst = singleSubst (HS.UnQual (HS.Ident arg)) e2'
            e1''  = applySubst subst e1'
        return ([], remainingArgs', e1'')

  -- Substitute type arguments of inlined function.
  inlineExpr' (HS.TypeAppExpr srcSpan e t exprType) = do
    (remainingTypeArgs, remainingArgs, e') <- inlineExpr' e
    case remainingTypeArgs of
      [] -> return ([], remainingArgs, HS.TypeAppExpr srcSpan e' t exprType)
      (typeArg : remainingTypeArgs') -> do
        let subst = singleSubst (HS.UnQual (HS.Ident typeArg)) t
            e''   = applySubst subst e'
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
