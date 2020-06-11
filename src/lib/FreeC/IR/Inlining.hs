-- | This module contains functions for inlining the definition of
--   functions into expressions or other function declarations.
--
--   Inlining is performed during the translation of recursive function
--   declarations to inline the definition of the non-recursive main
--   function into the recursive helper functions.

module FreeC.IR.Inlining where

import           Control.Monad                  ( unless )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map

import           FreeC.IR.SrcSpan
import           FreeC.IR.Subst
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty


-- | Inlines the right hand sides of the given function declarations into
--   the right hand sides of other function declarations.
inlineFuncDecls :: [IR.FuncDecl] -> IR.FuncDecl -> Converter IR.FuncDecl
inlineFuncDecls decls decl = do
  let rhs = IR.funcDeclRhs decl
  rhs' <- inlineExpr decls rhs
  return decl { IR.funcDeclRhs = rhs' }

-- | Inlines the right hand sides of the given function declarations into an
--   expression. This step is repeated until the expression remains unchanged
--   or no more function declarations are available.
--   That is done under the assumption that regarding a certain position
--   of the given expression every given function should be inlined at 
--   most once in order to avoid infinit inlining.
inlineExpr :: [IR.FuncDecl] -> IR.Expr -> Converter IR.Expr
inlineExpr []    = return
inlineExpr decls = inlineAndBind
 where
  -- | Maps the names of function declarations in 'decls' to the arguments
  --   and right hand sides of the functions.
  declMap :: Map IR.QName ([IR.TypeVarDecl], [IR.VarPat], IR.Expr)
  declMap = foldr insertFuncDecl Map.empty decls

  -- | Inserts a function declaration into 'declMap'.
  insertFuncDecl
    :: IR.FuncDecl
    -> Map IR.QName ([IR.TypeVarDecl], [IR.VarPat], IR.Expr)
    -> Map IR.QName ([IR.TypeVarDecl], [IR.VarPat], IR.Expr)
  insertFuncDecl funcDecl = Map.insert
    (IR.funcDeclQName funcDecl)
    ( IR.funcDeclTypeArgs funcDecl
    , IR.funcDeclArgs funcDecl
    , IR.funcDeclRhs funcDecl
    )

  -- | Applies 'inlineExpr'' on the given expression and wraps the result with
  --   lambda abstractions for the remaining arguments.
  --
  --   It is an error if not all type arguments of an inlined function are
  --   bound by visible type application expressions.
  inlineAndBind :: IR.Expr -> Converter IR.Expr
  inlineAndBind expr = do
    (remainingArgs, expr', name) <- inlineVisiblyApplied expr
    if null remainingArgs
    --(filter ((name /=) . IR.funcDeclQName) decls)--
    --inlineExpr decls expr'
      then if expr == expr'
        then return expr'
        else inlineExpr (filter ((name /=) . IR.funcDeclQName) decls) expr'
      else do
        let remainingArgPats = map IR.toVarPat remainingArgs
        return (IR.Lambda NoSrcSpan remainingArgPats expr' Nothing)

  -- | Applies 'inlineExpr'' on the given expression and reports an
  --   internal fatal error if not all type arguments have been
  --   applied visibly.
  inlineVisiblyApplied :: IR.Expr -> Converter ([String], IR.Expr, IR.QName)
  inlineVisiblyApplied e = do
    (remainingTypeArgs, remainingArgs, e', name) <- inlineExpr' e
    unless (null remainingTypeArgs)
      $  reportFatal
      $  Message (IR.exprSrcSpan e) Internal
      $  "Missing visible application of "
      ++ show (length remainingTypeArgs)
      ++ " type arguments in an application of '"
      ++ showPretty e
      ++ "'."
    return (remainingArgs, e', name)

  -- | Performs inlining on the given subexpression.
  --
  --   If a function is inlined, fresh free variables are introduced for the
  --   function arguments. The first two components of the returned tuple
  --   contain the names of the type variables and variables that still need
  --   to be bound. The last component of the returndes tuple is the qualified
  --   name of the inlined function.
  --   Function application and visible type application expressions
  --   automatically substitute the corresponding argument for
  --   the passed value.
  inlineExpr' :: IR.Expr -> Converter ([String], [String], IR.Expr, IR.QName)
  inlineExpr' var@(IR.Var _ name _) = case Map.lookup name declMap of
    Nothing                    -> return ([], [], var, emptyName)
    Just (typeArgs, args, rhs) -> do
      (typeArgs', rhs' ) <- renameTypeArgs typeArgs rhs
      (args'    , rhs'') <- renameArgs args rhs'
      return
        ( map IR.typeVarDeclIdent typeArgs'
        , map IR.varPatIdent      args'
        , rhs''
        , name
        )

  -- Substitute argument of inlined function and inline recursively in
  -- function arguments.
  inlineExpr' (IR.App srcSpan e1 e2 exprType) = do
    (remainingArgs, e1', name) <- inlineVisiblyApplied e1
    e2'                        <- inlineAndBind e2
    case remainingArgs of
      [] -> return ([], [], IR.App srcSpan e1' e2' exprType, name)
      (arg : remainingArgs') -> do
        let subst = singleSubst (IR.UnQual (IR.Ident arg)) e2'
            e1''  = applySubst subst e1'
        return ([], remainingArgs', e1'', name)

  -- Substitute type arguments of inlined function.
  inlineExpr' (IR.TypeAppExpr srcSpan e t exprType) = do
    (remainingTypeArgs, remainingArgs, e', name) <- inlineExpr' e
    case remainingTypeArgs of
      [] ->
        return ([], remainingArgs, IR.TypeAppExpr srcSpan e' t exprType, name)
      (typeArg : remainingTypeArgs') -> do
        let subst = singleSubst (IR.UnQual (IR.Ident typeArg)) t
            e''   = applySubst subst e'
        return (remainingTypeArgs', remainingArgs, e'', name)

  -- Inline recursively.
  inlineExpr' (IR.If srcSpan e1 e2 e3 exprType) = do
    e1' <- inlineAndBind e1
    e2' <- inlineAndBind e2
    e3' <- inlineAndBind e3
    return ([], [], IR.If srcSpan e1' e2' e3' exprType, emptyName)
  inlineExpr' (IR.Case srcSpan expr alts exprType) = do
    expr' <- inlineAndBind expr
    alts' <- mapM inlineAlt alts
    return ([], [], IR.Case srcSpan expr' alts' exprType, emptyName)
  inlineExpr' (IR.Lambda srcSpan varPats expr exprType) =
    shadowVarPats varPats $ do
      expr' <- inlineAndBind expr
      return ([], [], IR.Lambda srcSpan varPats expr' exprType, emptyName)

  -- All other expressions remain unchanged.
  inlineExpr' expr@(IR.Con _ _ _       ) = return ([], [], expr, emptyName)
  inlineExpr' expr@(IR.Undefined _ _   ) = return ([], [], expr, emptyName)
  inlineExpr' expr@(IR.ErrorExpr  _ _ _) = return ([], [], expr, emptyName)
  inlineExpr' expr@(IR.IntLiteral _ _ _) = return ([], [], expr, emptyName)

  -- | Performs inlining on the right hand side of the given @case@-expression
  --   alternative.
  inlineAlt :: IR.Alt -> Converter IR.Alt
  inlineAlt (IR.Alt srcSpan conPat varPats expr) = shadowVarPats varPats $ do
    expr' <- inlineAndBind expr
    return (IR.Alt srcSpan conPat varPats expr')

  --constant used to express a dummy value for QName
  emptyName = IR.UnQual (IR.Ident [])
