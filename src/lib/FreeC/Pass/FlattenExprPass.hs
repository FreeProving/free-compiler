-- | This module contains a compiler pass that analyses the right-hand sides of
--   function declaration and introduces @let@-expression with new variables
--   for each variable that occurs more than once on the right-hand sides.
--
--   = Examples
--
--   == Example 1
--
--   > twice :: Integer -> Integer
--   > twice (x :: Integer) = x + x
--
--   Should be transformed into
--
--   > twice :: Integer -> Maybe Integer
--   > twice (x :: Integer) = let (y :: Integer) = x in y + y
--
--   where @y@ is a fresh variable.
--
--   == Example 2
--
--   > twiceMaybe :: Maybe Integer -> Maybe Integer
--   > twiceMaybe (mx :: Maybe Integer) = case (mx :: Maybe Integer) of {
--   >     Nothing -> Nothing;
--   >     Just x  -> Just (x + x)
--   >   }
--
--   Should be transformed into
--
--   > twiceMaybe :: Maybe Integer -> Maybe Integer
--   > twiceMaybe (mx :: Maybe Integer) = case (mx :: Maybe Integer) of {
--   >     Nothing -> Nothing;
--   >     Just x  -> let y = x in Just (y + y)
--   >   }
--   where @y@ is a fresh variable.
--
--   == Example 3
--
--   > two :: Integer
--   > two = let x = 1 in x + x
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
--   First all subexpressions of each function declaration are checked for variables
--   occurring multiple times on the right hand sides of lambda abstractions or
--   @case@-expression alternatives. If found the variables are replaced by a
--   fresh variable and a @let@-binding is introduced binding the fresh variable
--   to the old one.
--
--   After all subexpressions are checked the right hand side of the function
--   declaration is checked as well.
--   Variables already bound by @let@-bindings are not counted.
--
--   == Postconditions
--
--   All shared variables on right-hand sides of function declarations are made
--   explicit by introducing @let@-expressions.
module FreeC.Pass.FlattenExprPass
  ( flattenExprPass
    -- * Testing Interface
  , flattenExpr
  ) where

import           Control.Monad           ( (>=>), mapAndUnzipM )
import           Data.Maybe              ( catMaybes )

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
flatExpr (IR.App _ lhs rhs _) typeArgs args = flatExpr lhs typeArgs (rhs : args)
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
flatExpr (IR.Trace srcSpan traceMsg traceExpr typeScheme) typeArgs args = do
    expr' <- flatExpr traceExpr [] []
    buildLet (IR.Trace srcSpan traceMsg expr' typeScheme) typeArgs args

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
        varName = (IR.UnQual $ IR.Ident varIdent)
        var     = IR.Var srcSpan varName (IR.exprTypeScheme expr)
    return (Just bind, var)
