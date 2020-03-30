-- | This module contains a compiler pass that applies η-conversions to
--   expressions such that all function and constructor applications are
--   fully applied.
--
--   An η-conversion is the conversion of a partially applied function
--   expression @f@ to a lambda expression @\\x -> f x@ that explicitly
--   applies the missing argument.
--
--  = Motivation
--
--   We have to perform η-conversions due to an optimization of the monadic
--   translation of function declarations.
--   An @n@-ary function declaration of type @τ₁ -> … -> τₙ -> τ@ is translated
--   to a function declaration of type @τ₁' -> … -> τₙ' -> τ'@ where @τᵢ'@ is
--   the translation of type @τᵢ@. However, an @n@-ary lambda abstraction of
--   the same type is translated to @m (τ₁' -> (τ₂ -> … -> τₙ -> τ)')@ where
--   @m@ is the target monad. That only the arguments but not the intermediate
--   results of function declarations are lifted to the monad, improves the
--   readability of generated function applications. Intermediate results don't
--   have to be bound since we know that partial applications cannot have an
--   effect.
--   This optimization does not work when functions are applied only partially.
--   Thus, we have to convert partial applications to full applications.
--
--   = Specification
--
--   == Preconditions
--
--   The arity of all constructors and functions must be known (i.e., there
--   must be corresponding environment entries).
--
--   == Translation
--
--   On the right-hand sides of function declarations, all of the largest
--   sub-expressions of the form
--
--   @
--   f @α₁ … @αₚ e₁ … eₘ
--   @
--
--   where @f@ is the name of an @n@-ary constructor or function declaration
--   and @m < n@ is replaced by a lambda abstraction
--
--   @
--   \\x₍ₘ₊₁₎ … xₙ -> f @α₁ … @αₚ e₁ … eₘ x₍ₘ₊₁₎ … xₙ
--   @
--
--   where @x₍ₘ₊₁₎ … xₙ@ are @n-m@ fresh variables.
--
--   == Postconditions
--
--   All applications of @n@-ary functions or constructors have at least @n@
--   arguments.

module Compiler.Pass.EtaConversionPass
  ( etaConversionPass
  )
where

import           Control.Monad                  ( replicateM )
import           Data.Maybe                     ( fromMaybe )

import           Compiler.Environment
import           Compiler.Environment.Fresh
import           Compiler.Environment.Scope
import           Compiler.IR.SrcSpan
import           Compiler.IR.Subterm
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Monad.Converter
import           Compiler.Pass

-- | Applies η-conversions to the right-hand sides of all function declarations
--   in the given module until all function and constructor applications are
--   fully applied.
etaConversionPass :: Pass HS.Module
etaConversionPass ast = do
  funcDecls' <- mapM etaConvertFuncDecl (HS.modFuncDecls ast)
  return ast { HS.modFuncDecls = funcDecls' }

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Applies 'etaConvertExpr' to the right-hand side of the given function
--   declaration.
etaConvertFuncDecl :: HS.FuncDecl -> Converter HS.FuncDecl
etaConvertFuncDecl funcDecl = do
  rhs' <- etaConvertExpr (HS.funcDeclRhs funcDecl)
  return funcDecl { HS.funcDeclRhs = rhs' }

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Applies η-conversions to the given expression and it's sub-expressions
--   until all function and constructor applications are fully applied.
etaConvertExpr :: HS.Expr -> Converter HS.Expr
etaConvertExpr expr = localEnv $ do
  arity <- arityOf expr
  xs    <- replicateM arity $ freshHaskellIdent freshArgPrefix
  expr' <- etaConvertSubExprs expr
  return (etaAbstractWith xs expr')

-- | Creates a lambda abstraction with the given arguments that immediatly
--   applies the given expression to the arguments.
etaAbstractWith :: [String] -> HS.Expr -> HS.Expr
etaAbstractWith xs expr | null xs   = expr
                        | otherwise = HS.Lambda NoSrcSpan argPats expr' Nothing
 where
  argPats  = map HS.toVarPat xs
  argExprs = map HS.varPatToExpr argPats
  expr'    = HS.app NoSrcSpan expr argExprs

-------------------------------------------------------------------------------
-- Sub-expressions                                                           --
-------------------------------------------------------------------------------

-- | Applies 'etaConvertExpr' to all sub-expressions of the given expression
--   except for the left-hand side of function applications.
etaConvertSubExprs :: HS.Expr -> Converter HS.Expr
-- If the expression is applied, it expects one argument less.
etaConvertSubExprs (HS.App srcSpan e1 e2 exprType) = do
  e1' <- etaConvertSubExprs e1
  e2' <- etaConvertExpr e2
  return (HS.App srcSpan e1' e2' exprType)

-- Apply η-conversion recursively.
etaConvertSubExprs expr@(HS.If _ _ _ _ _       ) = etaConvertSubExprs' expr
etaConvertSubExprs expr@(HS.Case   _ _ _ _     ) = etaConvertSubExprs' expr
etaConvertSubExprs expr@(HS.Lambda _ _ _ _     ) = etaConvertSubExprs' expr

-- Leave all other expressions unchanged.
etaConvertSubExprs expr@(HS.Con _ _ _          ) = return expr
etaConvertSubExprs expr@(HS.Var _ _ _          ) = return expr
etaConvertSubExprs expr@(HS.TypeAppExpr _ _ _ _) = return expr
etaConvertSubExprs expr@(HS.Undefined _ _      ) = return expr
etaConvertSubExprs expr@(HS.ErrorExpr  _ _ _   ) = return expr
etaConvertSubExprs expr@(HS.IntLiteral _ _ _   ) = return expr

-- | Applies 'etaConvertExpr' to all sub-expressions of the given expression.
etaConvertSubExprs' :: HS.Expr -> Converter HS.Expr
etaConvertSubExprs' expr = do
  let children = childTerms expr
  children' <- mapM etaConvertExpr children
  let Just expr' = replaceChildTerms expr children'
  return expr'

-------------------------------------------------------------------------------
-- Arity                                                                     --
-------------------------------------------------------------------------------

-- | Determines the number of arguments expected to be passed to the given
--   expression.
arityOf :: HS.Expr -> Converter Int
arityOf (HS.Con _ name _) = do
  arity <- inEnv $ lookupArity ValueScope name
  return (fromMaybe 0 arity)
arityOf (HS.Var _ name _) = do
  arity <- inEnv $ lookupArity ValueScope name
  return (fromMaybe 0 arity)
arityOf (HS.App _ e1 _ _) = do
  arity <- arityOf e1
  return (max 0 (arity - 1))

-- Visible type applications do not affect the function's arity.
arityOf (HS.TypeAppExpr _ e _ _) = arityOf e

-- All other expressions do not expect any arguments.
arityOf (HS.If _ _ _ _ _       ) = return 0
arityOf (HS.Case _ _ _ _       ) = return 0
arityOf (HS.Undefined _ _      ) = return 0
arityOf (HS.ErrorExpr  _ _ _   ) = return 0
arityOf (HS.IntLiteral _ _ _   ) = return 0
arityOf (HS.Lambda _ _ _ _     ) = return 0
