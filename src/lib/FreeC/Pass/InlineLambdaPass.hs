-- | This module contains a pass for inlining lambda abstractions that are
--   bound by bindings of @let@-expressions into the @in@-expressions.
--
--   The purpose of this pass is to avoid the generation of @call@ and @share@
--   operators for lambda abstractions. Since lambda abstractions are not
--   evaluated by any evaluation strategy until they are invoked, the inlining
--   does not change the semantics of the program. The inlining helps Coq's
--   termination checker sometimes if the lambda abstraction contains recursive
--   calls.
--
--   = Example
--
--   Expressions of the form
--
--   > let { f = \x -> e } in g f
--
--   are replaced by expressions of the form
--
--   > g (\x -> e)
--
--   = Specification
--
--   == Preconditions
--
--   All functions are fully applied (i.e., fully η-converted).
--
--   == Translation
--
--   For every @let@-expression
--
--   > let {x₁ = e₁ ; … ; xₙ = eₙ} in e
--
--   all bindings @xᵢ = eᵢ@ whose right-hand side @eᵢ@ is a lambda abstraction,
--   are removed and all occurences of @xᵢ@ in @e@ are replaced by @eᵢ@.
--
--   == Postconditions
--
--   There are no @let@-bindings whose right-hand side is a lambda-abstraction.
module FreeC.Pass.InlineLambdaPass
  ( inlineLambdaPass
    -- * Testing Interface
  , inlineLambdaExpr
  ) where

import           Data.Either           ( partitionEithers )

import           FreeC.IR.Subst
  ( Subst, applySubst, composeSubsts, singleSubst )
import           FreeC.IR.Subterm      ( mapSubterms )
import qualified FreeC.IR.Syntax       as IR
import           FreeC.Monad.Converter
import           FreeC.Pass

-- | Inlines all @let@-bindings for lambda abstractions that occur in the given
--   module.
inlineLambdaPass :: Pass IR.Module IR.Module
inlineLambdaPass ast = do
  funcDecls' <- mapM inlineLambdaFuncDecl (IR.modFuncDecls ast)
  return (IR.modWithFuncDecls funcDecls' ast)

-- | Applies 'inlineLambdaExpr' to the right-hand side of the given function
--   declaration.
inlineLambdaFuncDecl :: IR.FuncDecl -> Converter IR.FuncDecl
inlineLambdaFuncDecl funcDecl = do
  let rhs' = inlineLambdaExpr (IR.funcDeclRhs funcDecl)
  return funcDecl { IR.funcDeclRhs = rhs' }

-- | Inlines all lambda abstractions that are bound by bindings of
--   @let@-expressions in the given expression.
inlineLambdaExpr :: IR.Expr -> IR.Expr
inlineLambdaExpr = mapSubterms inlineLambdaExpr'

-- | Like 'inlineLambdaExpr', but does not inline lambda abstractions
--   recursively.
inlineLambdaExpr' :: IR.Expr -> IR.Expr
inlineLambdaExpr' expr@(IR.Let {})
  = let (substs, binds') = partitionEithers
          (map substLambdaOrBind (IR.letExprBinds expr))
        subst            = composeSubsts substs
        expr'            | null binds' = IR.letExprIn expr
                         | otherwise = expr { IR.letExprBinds = binds' }
    in applySubst subst expr'
inlineLambdaExpr' expr             = expr

-- | Creates a substitution that inlines the lambda abstraction that is bound
--   by the given binding or returns the binding unchanged if it does not bind
--   a lambda abstraction.
substLambdaOrBind :: IR.Bind -> Either (Subst IR.Expr) IR.Bind
substLambdaOrBind bind = case IR.bindExpr bind of
  expr@(IR.Lambda {}) -> Left
    (singleSubst (IR.varPatQName (IR.bindVarPat bind)) expr)
  _                   -> Right bind
