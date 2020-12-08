-- | This module contains a compiler pass that transforms all expressions from
--   function declarations into a flat form. An expression is "flat" if all
--   function and constructors are only applied to variables.
--
--   = Examples
--
--   == Example 1
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
--   For every function or constructor applications @f e₁ … eₙ@ where
--   @e₁, …, eₙ@ are arbitrary expressions the transformation generates
--   the following expression
--
--   > let {x₁ = e₁ ; … ; xₙ = eₙ} in f x₁ … xₙ
--
--   where @x₁, …, xₙ@ are fresh variables.
--   The @let@-bindings are only introduced if the corresponding expression is
--   not a variable. The translation is applied to the expressions @e₁, …, eₙ@
--   recursively.
--
--   == Postconditions
--
--   All applications of functions and constructors have the form @f x₁ … xₙ@
--   where @f@ is a function or constructor and @x₁, …, xₙ@ are variables.
module FreeC.Pass.FlattenExprPass
  ( flattenExprPass
    -- * Testing Interface
  , flattenExpr
  ) where

import           Control.Monad           ( mapAndUnzipM )
import           Data.Maybe              ( catMaybes )

import           FreeC.Environment       ( encapsulatesEffects )
import           FreeC.Environment.Fresh ( freshArgPrefix, freshHaskellIdent )
import           FreeC.IR.Subterm        ( childTerms, replaceChildTerms' )
import qualified FreeC.IR.Syntax         as IR
import           FreeC.Monad.Converter
import           FreeC.Pass

-- | Transforms all function declarations of a given module into the flat form.
flattenExprPass :: Pass IR.Module IR.Module
flattenExprPass ast = do
  funcDecls' <- mapM flattenFuncDecl (IR.modFuncDecls ast)
  return (IR.modWithFuncDecls funcDecls' ast)

-- | Flattens the expression on the right hand side of the given function
--   declaration.
flattenFuncDecl :: IR.FuncDecl -> Converter IR.FuncDecl
flattenFuncDecl funcDecl = do
  rhs' <- flattenExpr (IR.funcDeclRhs funcDecl)
  return funcDecl { IR.funcDeclRhs = rhs' }

-- | Flattens the given expression.
--
--   @let@-expressions are generated as deep as possible without duplicating @let@-expressions.
--
--   @let@-expressions are not generated for a function that should encapsulate
--   effects in its arguments.
flattenExpr :: IR.Expr -> Converter IR.Expr
flattenExpr expr = flattenExpr' expr [] []

-- | Like 'flattenExpr' but accumulates the type arguments and arguments the
--   expression has been applied to in the additional two arguments.
--
--   The arguments should be in flat form already.
flattenExpr' :: IR.Expr -> [IR.Type] -> [IR.Expr] -> Converter IR.Expr

-- Constructors always need to be flattened. Functions only need to be
-- flattened when they don't encapsulate effects.
flattenExpr' expr@(IR.Con _ _ _) typeArgs args = buildLet expr typeArgs args
flattenExpr' expr@(IR.Var srcSpan varName _) typeArgs args = do
  enapsulatesEffects <- inEnv $ encapsulatesEffects varName
  if enapsulatesEffects
    then return (IR.app srcSpan (IR.visibleTypeApp srcSpan expr typeArgs) args)
    else buildLet expr typeArgs args
-- Accumulate arguments and type arguments.
flattenExpr' (IR.App _ expr arg _) typeArgs args = do
  arg' <- flattenExpr arg
  flattenExpr' expr typeArgs (arg' : args)
flattenExpr' (IR.TypeAppExpr _ expr typeArg _) typeArgs args = flattenExpr' expr
  (typeArg : typeArgs) args
-- Recursively flatten all other expressions.
flattenExpr' expr typeArgs args = do
  children' <- mapM flattenExpr (childTerms expr)
  buildLet (replaceChildTerms' expr children') typeArgs args

-- | Builds a @let@-expression that binds the given arguments to fresh
--   variables and applies the given expression to the provided type arguments
--   and fresh variables.
--
--   If an argument is a variable already, it is not bound again.
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
  -- | Creates a @let@-binding that binds the given expression to a fresh
  --   variable.
  --
  --   Returns the binding and a variable expression for the fresh variable.
  --   No new binding is generated if the given expression is a variable
  --   already.
  buildBind :: IR.Expr -> Converter (Maybe IR.Bind, IR.Expr)
  buildBind expr@IR.Var {} = return (Nothing, expr)
  buildBind expr           = do
    varIdent <- freshHaskellIdent freshArgPrefix
    let srcSpan = IR.exprSrcSpan expr
        varPat  = IR.VarPat srcSpan varIdent Nothing False
        bind    = IR.Bind srcSpan varPat expr
        varName = IR.UnQual $ IR.Ident varIdent
        var     = IR.Var srcSpan varName (IR.exprTypeScheme expr)
    return (Just bind, var)
