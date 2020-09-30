-- | This module contains a compiler pass that transforms all expressions from
--   function declarations into a "flattened form" meaning that all contained
--   functions are only applied on constants or variables.
--
--   = Examples
--
--   == Example 1
--
--
--   The following function does contain functions, which are applied on other
--   function calls.
--
--   > dot :: (b -> c) -> (a -> b) -> a -> c
--   > dot (f :: b -> c) (g :: a -> b) (x :: a) = f (g x)
--
--   The pass transforms the example the following way.
--
--   > dot :: (b -> c) -> (a -> b) -> a -> c
--   > dot (f :: b -> c) (g :: a -> b) (x :: a) = let {y = g x} in f y
--
--   where @y@ is a fresh variable.
--
--
--   == Example 2
--
--   > dollar :: (a -> b) -> a -> b
--   > dollar (f :: a -> b) (x :: a) = f x
--
--   Should not be changed by the transformation.
--
--   = Specification
--
--   == Preconditions
--
--   There are no special requirements.
--
--   == Translation
--
--   == Postconditions
--
--
module FreeC.Pass.FlattenExprPass
  ( flattenExprPass
    -- * Testing Interface
  , flattenExpr
  ) where

import           Control.Monad           ( (>=>), mapAndUnzipM )
import           Data.Maybe              ( catMaybes )

import           FreeC.Environment       ( encapsulatesEffects )
import           FreeC.Environment.Fresh ( freshArgPrefix, freshHaskellIdent )
import qualified FreeC.IR.Syntax         as IR
import           FreeC.Monad.Converter
import           FreeC.Pass

flattenExprPass :: Pass IR.Module IR.Module
flattenExprPass ast = do
  funcDecls' <- mapM flatFuncDecl (IR.modFuncDecls ast)
  return ast { IR.modFuncDecls = funcDecls' }

flatFuncDecl :: IR.FuncDecl -> Converter IR.FuncDecl
flatFuncDecl funcDecl = do
  rhs' <- (flattenExpr >=> combineLets) (IR.funcDeclRhs funcDecl)
  return funcDecl { IR.funcDeclRhs = rhs' }

combineLets :: IR.Expr -> Converter IR.Expr
combineLets = return

flattenExpr :: IR.Expr -> Converter IR.Expr
flattenExpr expr = flatExpr expr [] []

flatExpr :: IR.Expr -> [IR.Type] -> [IR.Expr] -> Converter IR.Expr
flatExpr (IR.Con srcSpan conName typeScheme) typeArgs args = buildLet
  (IR.Con srcSpan conName typeScheme) typeArgs args
flatExpr (IR.Var srcSpan varName typeScheme) typeArgs args = buildLet
  (IR.Var srcSpan varName typeScheme) typeArgs args
flatExpr (IR.App srcSpan lhs rhs typeScheme) typeArgs args = do
  encEffects <- shouldEncapsulateEffects lhs
  if encEffects
    then do
      lhs' <- flatExpr lhs [] []
      rhs' <- flatExpr rhs [] []
      return $ IR.App srcSpan lhs' rhs' typeScheme
    else flatExpr lhs typeArgs (rhs : args)
flatExpr (IR.TypeAppExpr _ expr typeArg _) typeArgs args = flatExpr expr
  (typeArg : typeArgs) args
flatExpr (IR.If srcSpan e1 e2 e3 typeScheme) typeArgs args = do
  e1' <- flatExpr e1 [] []
  e2' <- flatExpr e2 [] []
  e3' <- flatExpr e3 [] []
  buildLet (IR.If srcSpan e1' e2' e3' typeScheme) typeArgs args
flatExpr (IR.Case srcSpan scrutinee alts typeScheme) typeArgs args = do
  scrutinee' <- flatExpr scrutinee [] []
  alts' <- mapM flatAlt alts
  buildLet (IR.Case srcSpan scrutinee' alts' typeScheme) typeArgs args
 where
  flatAlt :: IR.Alt -> Converter IR.Alt
  flatAlt (IR.Alt altSrcSpan conPat varPats rhs) = do
    rhs' <- flatExpr rhs [] []
    return $ IR.Alt altSrcSpan conPat varPats rhs'
flatExpr (IR.Undefined srcSpan typeScheme) typeArgs args = buildLet
  (IR.Undefined srcSpan typeScheme) typeArgs args
flatExpr (IR.ErrorExpr srcSpan exprMsg typeScheme) typeArgs args = buildLet
  (IR.ErrorExpr srcSpan exprMsg typeScheme) typeArgs args
flatExpr (IR.IntLiteral srcSpan literalValue typeScheme) typeArgs args
  = buildLet (IR.IntLiteral srcSpan literalValue typeScheme) typeArgs args
flatExpr (IR.Lambda srcSpan exprArgs rhs typeScheme) typeArgs args = do
  rhs' <- flatExpr rhs [] []
  buildLet (IR.Lambda srcSpan exprArgs rhs' typeScheme) typeArgs args
flatExpr (IR.Let bindSrcSpan binds expr typeScheme) typeArgs args = do
  binds' <- mapM flatBind binds
  expr' <- flatExpr expr [] []
  buildLet (IR.Let bindSrcSpan binds' expr' typeScheme) typeArgs args
 where
  flatBind :: IR.Bind -> Converter IR.Bind
  flatBind (IR.Bind srcSpan varPat rhs) = do
    rhs' <- flatExpr rhs [] []
    return $ IR.Bind srcSpan varPat rhs'

buildLet :: IR.Expr -> [IR.Type] -> [IR.Expr] -> Converter IR.Expr
buildLet e' typeArgs args = do
  (mBinds, vars) <- mapAndUnzipM buildBind args
  let binds   = catMaybes mBinds
      srcSpan = IR.exprSrcSpan e'
      expr    = IR.app srcSpan (IR.visibleTypeApp srcSpan e' typeArgs) vars
  if null binds
    then return expr
    else return $ IR.Let srcSpan binds expr (IR.exprTypeScheme e')
 where
  buildBind :: IR.Expr -> Converter (Maybe IR.Bind, IR.Expr)
  buildBind v@IR.Var {} = return (Nothing, v)
  buildBind expr        = do
    expr' <- flatExpr expr [] []
    varIdent <- freshHaskellIdent freshArgPrefix
    let srcSpan = IR.exprSrcSpan expr
        varPat  = IR.VarPat srcSpan varIdent Nothing False
        bind    = IR.Bind srcSpan varPat expr'
        varName = IR.UnQual $ IR.Ident varIdent
        var     = IR.Var srcSpan varName (IR.exprTypeScheme expr)
    return (Just bind, var)

-- | Whether an expression is an application of a function that encapsulates
--   effects.
shouldEncapsulateEffects :: IR.Expr -> Converter Bool
shouldEncapsulateEffects expr = case IR.getFuncName expr of
  Nothing   -> return False
  Just name -> inEnv $ encapsulatesEffects name

