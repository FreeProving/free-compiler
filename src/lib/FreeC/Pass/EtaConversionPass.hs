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
--   However, on the top-level, we add the missing arguments to the left-hand
--   and right-hand sides of the function rule explicitly, without a lambda
--   abstraction.
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
--   > f (e₁ :: τ₁) … (eₖ :: τₖ) :: τ'₁ -> … -> τ'ₙ₋ₘ -> τ =
--   >     g @α₁ … @αₚ e₁ … eₘ
--
--   where @g@ is the name of an @n@-ary constructor or function declaration
--   and @m < n@. This declaration is then replaced by
--
--   > f (e₁ :: τ₁) … (eₖ :: τₖ) (x₍ₘ₊₁₎ :: τ'₁) … (xₙ :: τ'ₙ₋ₘ) :: τ =
--   >     g @α₁ … @αₚ e₁ … eₘ x₍ₘ₊₁₎ … xₙ
--
--   where x₍ₘ₊₁₎ … xₙ are @n-m@ fresh variables.
--
--   If a function rule has several alternatives for the right-hand side
--   through (possibly nested) if or case expressions, the number of added
--   arguments is determined by the minimum number of missing arguments for an
--   alternative on the right-hand side.
--
--   Additionally, on the right-hand sides of function declarations, all of the
--   largest sub-expressions of the form
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
--   Both types of η-conversion may also be applied to the same expression.
--   For example, the function
--
--  > f (e₁ :: τ₁) ::  τ₂ -> τ₃ -> τ = case e₁ of {
--  >     c₁ -> g;
--  >     c₂ -> h
--  >   }
--
--  where @c₁@ and @c₂@ are the constructors of @τ₁@,
--  @g@ is a binary function of type @τ₂ -> τ₃ -> τ@, and
--  @h@ is a unary function of type @τ₂ -> (τ₃ -> τ)@,
--  will be converted to
--
--  > f (e₁ :: τ₁) (x :: τ₂) :: τ₃ -> τ = case e₁ of {
--  >     c₁ -> \y -> g x y;
--  >     c₂ -> h x
--  >   }
--
--   == Postconditions
--
--   All applications of @n@-ary functions or constructors have at least @n@
--   arguments.
module FreeC.Pass.EtaConversionPass
  ( etaConversionPass
    -- * Testing Interface
  , etaConvertFuncDecl
  , etaConvertExpr
  ) where

import           Control.Monad ( replicateM )
import           Data.Maybe ( fromJust, fromMaybe )

import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.Fresh
import           FreeC.IR.SrcSpan
import           FreeC.IR.Subterm
import qualified FreeC.IR.Syntax as IR
import           FreeC.Monad.Converter
import           FreeC.Pass
-- temporary import; TODO: move this pass before the TypeSignaturePass.
import           FreeC.Pass.TypeSignaturePass ( splitFuncType )

-- | Applies η-conversions to the right-hand sides of all function declarations
--   in the given module until all function and constructor applications are
--   fully applied.
etaConversionPass :: Pass IR.Module
etaConversionPass ast = do
  funcDecls' <- etaConvertFuncDecls (IR.modFuncDecls ast) []
  return ast { IR.modFuncDecls = funcDecls' }

-------------------------------------------------------------------------------
-- Function Declarations                                                     --
-------------------------------------------------------------------------------
-- | Makes sure that all occurring functions are fully applied
--   by calling 'etaConvertFuncDecl' on each of them.
--
--   If the type of a function declaration changes due to a top-level
--   η-conversion, the procedure is performed recursively on all
--   previously converted function declarations.
--   This ensures that all functions, including mutually-recursive
--   functions, are fully applied correctly.
--   The function's first argument represents the function
--   declarations yet to be converted.
--   The function's second argument is an accumulator for already
--   converted functions that is needed in case they must be
--   re-converted recursively.
etaConvertFuncDecls
  :: [IR.FuncDecl] -> [IR.FuncDecl] -> Converter [IR.FuncDecl]
etaConvertFuncDecls [] newFuncDecls         = return newFuncDecls
etaConvertFuncDecls (fd : fds) newFuncDecls = do
  newFuncDecl <- etaConvertFuncDecl fd
  if IR.funcDeclReturnType newFuncDecl /= IR.funcDeclReturnType fd
    then etaConvertFuncDecls (newFuncDecls ++ (newFuncDecl : fds)) []
    else etaConvertFuncDecls fds (newFuncDecls ++ [newFuncDecl])

-- | Applies appropriate η-conversions to a function declaration.
--
--   Depending on the presence or absence of missing top-level arguments,
--   the function uses 'etaConvertTopLevel' or 'etaConvertExpr' to ensure
--   all functions and constructors on the right-hand side are fully applied.
--   The missing top-level arguments are also added to the left-hand
--   side of the declaration and the function's type and the environment
--   are updated accordingly.
etaConvertFuncDecl :: IR.FuncDecl -> Converter IR.FuncDecl
etaConvertFuncDecl funcDecl = do
  let rhs = IR.funcDeclRhs funcDecl
  newArgNumber <- findMinMissingArguments rhs
  newFuncDecl <- localEnv
    $ do
      newArgIdents
        <- replicateM newArgNumber $ freshHaskellIdent freshArgPrefix
      modifyTopLevel funcDecl rhs newArgIdents
     -- Update the environment with the new type and arguments.
  Just entry <- inEnv $ lookupEntry IR.ValueScope (IR.funcDeclQName funcDecl)
  modifyEnv
    $ addEntry entry
    { entryArity      = length (IR.funcDeclArgs newFuncDecl)
    , entryArgTypes   = map (fromJust . IR.varPatType)
        (IR.funcDeclArgs newFuncDecl)
    , entryReturnType = fromJust $ IR.funcDeclReturnType newFuncDecl
    }
  return newFuncDecl

-- | Computes a new function declaration with all missing top-level arguments.
modifyTopLevel :: IR.FuncDecl -> IR.Expr -> [String] -> Converter IR.FuncDecl
modifyTopLevel funcDecl rhs newArgIdents = do
  -- Compute the function's new (uncurried) type. Assumes that funcDecl's
  -- return type is known.
  (newArgTypes, returnType) <- splitFuncType (IR.funcDeclQName funcDecl)
    (map IR.toVarPat newArgIdents) (fromJust $ IR.funcDeclReturnType funcDecl)
  -- Compute the function's new arguments and add them to the argument list.
  let newArgs = map ($ False)
        $ zipWith (IR.VarPat NoSrcSpan) newArgIdents (map Just newArgTypes)
  let vars' = IR.funcDeclArgs funcDecl ++ newArgs
  -- Compute the new right-hand side.
  rhs' <- etaConvertTopLevel newArgs rhs
  -- Update the function declaration's attributes.
  return funcDecl { IR.funcDeclArgs       = vars'
                  , IR.funcDeclReturnType = Just returnType
                  , IR.funcDeclRhs        = rhs'
                  }

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------
-- | Applies all top-level alternatives of an expression to their missing
--   arguments and calls 'etaConvertExpr' on the result to convert any
--   occurring lower-level partial applications.
etaConvertTopLevel :: [IR.VarPat] -> IR.Expr -> Converter IR.Expr

-- If there is more than one alternative, apply the conversion to
-- all alternatives.
etaConvertTopLevel argPats expr@(IR.If _ _ _ _ _)
  = etaConvertAlternatives argPats expr
etaConvertTopLevel argPats expr@(IR.Case _ _ _ _)
  = etaConvertAlternatives argPats expr
-- If there is only one alternative, apply it to the newly-added arguments,
-- then apply @etaConvertExpr@ to it to make so the expression and its sub
-- expressions are fully applied.
etaConvertTopLevel argPats expr = localEnv
  $ do
    let argExprs = map IR.varPatToExpr argPats
    -- Apply expression to missing arguments and perform eta-conversion on the
    -- resulting expression.
    etaConvertExpr $ IR.app NoSrcSpan expr argExprs

-- | Calls @etaConvertTopLevel@ on all alternatives in an if or case
--   expression.
etaConvertAlternatives :: [IR.VarPat] -> IR.Expr -> Converter IR.Expr
etaConvertAlternatives argPats expr = do
  -- The first child term of an if or case expression is the condition/the
  -- scrutinee and should remain unchanged.
  let (e : subterms) = childTerms expr
  subterms' <- mapM (etaConvertTopLevel argPats) subterms
  let Just expr' = replaceChildTerms expr (e : subterms')
  return expr'

-- | Applies η-conversions to the given expression and its sub-expressions.
--   until all function and constructor applications are fully applied.
etaConvertExpr :: IR.Expr -> Converter IR.Expr
etaConvertExpr expr = localEnv
  $ do
    arity <- arityOf expr
    xs <- replicateM arity $ freshHaskellIdent freshArgPrefix
    expr' <- etaConvertSubExprs expr
    return (etaAbstractWith xs expr')

-- | Creates a lambda abstraction with the given arguments that immediately
--   applies the given expression to the arguments.
etaAbstractWith :: [String] -> IR.Expr -> IR.Expr
etaAbstractWith xs expr
  | null xs = expr
  | otherwise = IR.Lambda NoSrcSpan argPats expr' Nothing
 where
   argPats  = map IR.toVarPat xs

   argExprs = map IR.varPatToExpr argPats

   expr'    = IR.app NoSrcSpan expr argExprs

-------------------------------------------------------------------------------
-- Sub-Expressions                                                           --
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
etaConvertSubExprs expr@(IR.If _ _ _ _ _)          = etaConvertSubExprs' expr
etaConvertSubExprs expr@(IR.Case _ _ _ _)          = etaConvertSubExprs' expr
etaConvertSubExprs expr@(IR.Lambda _ _ _ _)        = etaConvertSubExprs' expr
etaConvertSubExprs expr@(IR.Let _ _ _ _)           = etaConvertSubExprs' expr
-- Leave all other expressions unchanged.
etaConvertSubExprs expr@(IR.Con _ _ _)             = return expr
etaConvertSubExprs expr@(IR.Var _ _ _)             = return expr
etaConvertSubExprs expr@(IR.TypeAppExpr _ _ _ _)   = return expr
etaConvertSubExprs expr@(IR.Undefined _ _)         = return expr
etaConvertSubExprs expr@(IR.ErrorExpr _ _ _)       = return expr
etaConvertSubExprs expr@(IR.IntLiteral _ _ _)      = return expr

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
-- | Finds the minimum number of missing arguments among the alternatives
--   for the right-hand side of a function declaration.
findMinMissingArguments :: IR.Expr -> Converter Int
findMinMissingArguments (IR.If _ _ e1 e2 _)
  = minimum <$> mapM findMinMissingArguments [e1, e2]
findMinMissingArguments (IR.Case _ _ alts _) = minimum
  <$> mapM (findMinMissingArguments . IR.altRhs) alts
-- Any expression that isn't an if or case expression only has one
-- option for the number of missing arguments, namely the arity of the
-- expression.
findMinMissingArguments expr = arityOf expr

-- | Determines the number of arguments expected to be passed to the given
--   expression.
arityOf :: IR.Expr -> Converter Int
arityOf (IR.Con _ name _)        = do
  arity <- inEnv $ lookupArity IR.ValueScope name
  return (fromMaybe 0 arity)
arityOf (IR.Var _ name _)        = do
  arity <- inEnv $ lookupArity IR.ValueScope name
  return (fromMaybe 0 arity)
arityOf (IR.App _ e1 _ _)        = do
  arity <- arityOf e1
  return (max 0 (arity - 1))
-- Visible type applications do not affect the function's arity.
arityOf (IR.TypeAppExpr _ e _ _) = arityOf e
-- All other expressions do not expect any arguments.
arityOf (IR.If _ _ _ _ _)        = return 0
arityOf (IR.Case _ _ _ _)        = return 0
arityOf (IR.Undefined _ _)       = return 0
arityOf (IR.ErrorExpr _ _ _)     = return 0
arityOf (IR.IntLiteral _ _ _)    = return 0
arityOf (IR.Lambda _ _ _ _)      = return 0
arityOf (IR.Let _ _ _ _)         = return 0
