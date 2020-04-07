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

module FreeC.Pass.EtaConversionPass
  ( etaConversionPass
    -- * Testing interface
  , etaConvertExpr
  )
where

import           Control.Monad                  ( replicateM )
import           Data.Maybe                     ( fromMaybe )

import           FreeC.Environment
import           FreeC.Environment.Fresh
import           FreeC.Environment.Scope
import           FreeC.IR.SrcSpan
import           FreeC.IR.Subterm
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Pass

-- | Applies η-conversions to the right-hand sides of all function declarations
--   in the given module until all function and constructor applications are
--   fully applied.
etaConversionPass :: Pass IR.Module
etaConversionPass ast = do
  funcDecls' <- mapM etaConvertFuncDecl (IR.modFuncDecls ast)
  return ast { IR.modFuncDecls = funcDecls' }

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Applies 'etaConvertExpr' to the right-hand side of the given function
--   declaration.
etaConvertFuncDecl :: IR.FuncDecl -> Converter IR.FuncDecl
etaConvertFuncDecl funcDecl = do
  rhs' <- etaConvertExpr (IR.funcDeclRhs funcDecl)
  return funcDecl { IR.funcDeclRhs = rhs' }

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Applies η-conversions to the given expression and it's sub-expressions
--   until all function and constructor applications are fully applied.
etaConvertExpr :: IR.Expr -> Converter IR.Expr
etaConvertExpr expr = localEnv $ do
  arity <- arityOf expr
  xs    <- replicateM arity $ freshHaskellIdent freshArgPrefix
  expr' <- etaConvertSubExprs expr
  return (etaAbstractWith xs expr')

-- | Creates a lambda abstraction with the given arguments that immediatly
--   applies the given expression to the arguments.
etaAbstractWith :: [String] -> IR.Expr -> IR.Expr
etaAbstractWith xs expr | null xs   = expr
                        | otherwise = IR.Lambda NoSrcSpan argPats expr' Nothing
 where
  argPats  = map IR.toVarPat xs
  argExprs = map IR.varPatToExpr argPats
  expr'    = IR.app NoSrcSpan expr argExprs

-------------------------------------------------------------------------------
-- Sub-expressions                                                           --
-------------------------------------------------------------------------------

-- | Applies 'etaConvertExpr' to all sub-expressions of the given expression
--   except for the left-hand side of function applications.
etaConvertSubExprs :: IR.Expr -> Converter IR.Expr
-- If the expression is applied, it expects one argument less.
etaConvertSubExprs (IR.App srcSpan e1 e2 exprType) = do
  e1' <- etaConvertSubExprs e1
  e2' <- etaConvertExpr e2
  return (IR.App srcSpan e1' e2' exprType)

-- Apply η-conversion recursively.
etaConvertSubExprs expr@(IR.If _ _ _ _ _       ) = etaConvertSubExprs' expr
etaConvertSubExprs expr@(IR.Case   _ _ _ _     ) = etaConvertSubExprs' expr
etaConvertSubExprs expr@(IR.Lambda _ _ _ _     ) = etaConvertSubExprs' expr

-- Leave all other expressions unchanged.
etaConvertSubExprs expr@(IR.Con _ _ _          ) = return expr
etaConvertSubExprs expr@(IR.Var _ _ _          ) = return expr
etaConvertSubExprs expr@(IR.TypeAppExpr _ _ _ _) = return expr
etaConvertSubExprs expr@(IR.Undefined _ _      ) = return expr
etaConvertSubExprs expr@(IR.ErrorExpr  _ _ _   ) = return expr
etaConvertSubExprs expr@(IR.IntLiteral _ _ _   ) = return expr

-- | Applies 'etaConvertExpr' to all sub-expressions of the given expression.
etaConvertSubExprs' :: IR.Expr -> Converter IR.Expr
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
arityOf :: IR.Expr -> Converter Int
arityOf (IR.Con _ name _) = do
  arity <- inEnv $ lookupArity ValueScope name
  return (fromMaybe 0 arity)
arityOf (IR.Var _ name _) = do
  arity <- inEnv $ lookupArity ValueScope name
  return (fromMaybe 0 arity)
arityOf (IR.App _ e1 _ _) = do
  arity <- arityOf e1
  return (max 0 (arity - 1))

-- Visible type applications do not affect the function's arity.
arityOf (IR.TypeAppExpr _ e _ _) = arityOf e

-- All other expressions do not expect any arguments.
arityOf (IR.If _ _ _ _ _       ) = return 0
arityOf (IR.Case _ _ _ _       ) = return 0
arityOf (IR.Undefined _ _      ) = return 0
arityOf (IR.ErrorExpr  _ _ _   ) = return 0
arityOf (IR.IntLiteral _ _ _   ) = return 0
arityOf (IR.Lambda _ _ _ _     ) = return 0
