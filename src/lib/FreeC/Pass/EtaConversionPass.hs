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
--   We differentiate between top-level partial applications (i.e. when a 
--   function is defined as the partial application of another defined function 
--   or constructor) and partial applications that occur in the arguments of 
--   the function declaration's right-hand side. 
-- 
--   We perform regular η-conversions on partial applications in proper 
--   subexpressions of a function declaration's right-hand side. 
-- 
--   However, on the top-level, we add the missing arguments to the left-hand and
--   right-hand sides of the function rule explicitly, without a lambda abstraction. 
--   This is an optimization that allows the compiler to avoid some unnecessary 
--   monadic lifting.
--
--   = Specification
--
--   == Preconditions
--
--   The arity of all constructors and functions must be known (i.e., there
--   must be corresponding environment entries) and all function declarations 
--   must be type annotated.
--
--   == Translation
--
--   Assume that we have the following function declaration. 
--
--   > f e₁ … eₖ = g @α₁ … @αₚ e₁ … eₘ
--
--   where @g@ is the name of an @n@-ary constructor or function declaration and 
--   @m < n@. This declaration is then replaced by 
--   > f e₁ … eₖ x₍ₘ₊₁₎ … xₙ = g @α₁ … @αₚ e₁ … eₘ x₍ₘ₊₁₎ … xₙ
--   
--   where x₍ₘ₊₁₎ … xₙ are @n-m@ fresh variables. 
--
--   Additionally, on the right-hand sides of function declarations, all of the largest
--   proper sub-expressions of the form
--
--   > h @α₁ … @αᵣ e₁ … eₗ
--
--   where @h@ is the name of an @p@-ary constructor or function declaration
--   and @l < p@ are replaced by a lambda abstraction
--
--   > \y₍ₗ₊₁₎ … yₚ -> f @α₁ … @αᵣ e₁ … eₘ y₍ₗ₊₁₎ … yₚ
--
--   where @y₍ₗ₊₁₎ … yₚ@ are @p-l@ fresh variables.
--
--   == Postconditions
--
--   All applications of @n@-ary functions or constructors have at least @n@
--   arguments.

module FreeC.Pass.EtaConversionPass
  ( etaConversionPass
    -- * Testing interface
  , etaConvertFuncDecl
  , etaConvertExpr
  )
where

import           Control.Monad                  ( replicateM )
import           Data.Maybe                     ( fromMaybe
                                                , fromJust
                                                )

import           FreeC.Environment
import           FreeC.Environment.Fresh
import           FreeC.Environment.Entry
import           FreeC.IR.SrcSpan
import           FreeC.IR.Subterm
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Pass
-- temporary import; ideally, this pass should be moved before the TypeSignaturePass.
import 		 FreeC.Pass.TypeSignaturePass ( splitFuncType )

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

-- | Applies 'etaConvertTopLevelRhs' to the right-hand side of the given function
--   declaration to ensure all functions and constructors on the right-hand side 
--   are fully applied. 
--   The missing top-level arguments are also added to the left-hand side of the 
--   declaration and the function's type and the environment are updated accordingly. 
etaConvertFuncDecl :: IR.FuncDecl -> Converter IR.FuncDecl
etaConvertFuncDecl funcDecl = do
  let rhs = IR.funcDeclRhs funcDecl
  newArgIdents <- generateFullArgumentList rhs
  -- Compute the function's new (uncurried) type. Assumes that funcDecl's return type has already been inferred.
  (newArgTypes, returnType) <- splitFuncType
	(IR.funcDeclQName funcDecl)
	(map IR.toVarPat newArgIdents)
        (fromJust $ IR.funcDeclReturnType funcDecl)
  -- Compute the function's new arguments and add them to the argument list.
  let newArgs =
        zipWith (IR.VarPat NoSrcSpan) newArgIdents (map Just newArgTypes)
  let vars' = IR.funcDeclArgs funcDecl ++ newArgs
  -- Compute the new right-hand side.
  rhs'       <- etaConvertTopLevelRhs newArgs rhs
  -- Update the environment with the new type and arguments.
  Just entry <- inEnv $ lookupEntry IR.ValueScope (IR.funcDeclQName funcDecl)
  modifyEnv $ addEntry entry { entryArity      = length vars'
                             , entryArgTypes   = map IR.varPatType vars'
                             , entryReturnType = Just returnType
                             }
  -- Update the function declaration's attributes.
  return funcDecl { IR.funcDeclArgs       = vars'
                  , IR.funcDeclReturnType = Just returnType
                  , IR.funcDeclRhs        = rhs'
                  }

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Applies a function declaration's or constructor's right-hand side to its 
--   missing arguments.
--   Regular η-conversions are performed for the right-hand side's proper subexpressions 
--   via 'etaConvertSubExprs'.
etaConvertTopLevelRhs :: [IR.VarPat] -> IR.Expr -> Converter IR.Expr
etaConvertTopLevelRhs argPats expr = localEnv $ do
  expr' <- etaConvertSubExprs expr
  let argExprs = map IR.varPatToExpr argPats
  return $ IR.app NoSrcSpan expr' argExprs


-- | Applies η-conversions to the given expression and its sub-expressions
--   until all function and constructor applications are fully applied.
etaConvertExpr :: IR.Expr -> Converter IR.Expr
etaConvertExpr expr = localEnv $ do
  xs    <- generateFullArgumentList expr
  expr' <- etaConvertSubExprs expr
  return (etaAbstractWith xs expr')

-- | Creates a lambda abstraction with the given arguments that immediately
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
  arity <- inEnv $ lookupArity IR.ValueScope name
  return (fromMaybe 0 arity)
arityOf (IR.Var _ name _) = do
  arity <- inEnv $ lookupArity IR.ValueScope name
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

-------------------------------------------------------------------------------
-- Helper functions                                                                     --
-------------------------------------------------------------------------------

-- | Generates fresh identifiers for all missing arguments of an expression. 
generateFullArgumentList :: IR.Expr -> Converter [String]
generateFullArgumentList expr = localEnv $ do
  arity <- arityOf expr
  replicateM arity $ freshHaskellIdent freshArgPrefix
