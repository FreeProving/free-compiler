-- | This module contains a function for infering the type of an expression.

module Compiler.Analysis.TypeInference
  ( inferExprType
  )
where

import           Control.Monad.Extra            ( ifM )
import           Control.Monad.Writer

import           Compiler.Analysis.DependencyExtraction
                                                ( typeVars )
import           Compiler.Environment
import           Compiler.Environment.Fresh
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Haskell.Subst
import           Compiler.Haskell.Unification
import           Compiler.Monad.Converter

-- | Tries to infer the type of the given expression from the current context
--   and abstracts it's type to a type schema.
inferExprType :: HS.Expr -> Converter HS.TypeSchema
inferExprType expr = localEnv $ do
  -- TODO rename variables in expr
  typeVar    <- freshTypeVar
  (ps, eqns) <- execWriterT $ simplifyTypedExpr expr typeVar
  mgu        <- unifyEquations (makeTypeEquations ps ++ eqns)
  exprType   <- applySubst mgu typeVar
  abstractTypeSchema exprType

-------------------------------------------------------------------------------
-- Simplification of expression/type                                         --
-------------------------------------------------------------------------------

-- | A pair of a variable name and it's type.
type TypedVar = (HS.VarName, HS.Type)

-- | A type equation.
type TypeEquation = (HS.Type, HS.Type)

-- | A writer monad that allows 'simplifyTypedExpr' to generate 'TypedVar's
--   and 'TypeEquation's implicitly.
type TypedExprSimplifier a = WriterT ([TypedVar], [TypeEquation]) Converter a

-- | Adds a 'TypedVar' entry to a 'TypedExprSimplifier'.
addVarType :: HS.QName -> HS.Type -> TypedExprSimplifier ()
addVarType v t = tell ([(v, t)], [])

-- | Adds a 'TypeEquation' entry to a 'TypedExprSimplifier'.
addTypeEquation :: HS.Type -> HS.Type -> TypedExprSimplifier ()
addTypeEquation t t' = tell ([], [(t, t')])

-- | Instantiates the type schema of the function or constructor with the
--   given name and adds a 'TypeEquation' for the resulting type and the
--   given type.
addTypeEquationFor :: HS.QName -> HS.Type -> TypedExprSimplifier ()
addTypeEquationFor name resType = do
  Just typeSchema <- lift $ inEnv $ lookupTypeSchema ValueScope name
  funcType        <- lift $ instantiateTypeSchema typeSchema
  addTypeEquation funcType resType

-- | Simplifies expression/type pairs to pairs of variables and types and
--   type equations.
simplifyTypedExpr :: HS.Expr -> HS.Type -> TypedExprSimplifier ()

-- | If @f :: τ@ is a predefined function with @f :: forall α₀ … αₙ. τ'@, then
--   then @τ = σ(τ')@ with @σ = { α₀ ↦ β₀, …, αₙ ↦ βₙ }@ and @β₀, …, βₙ@ new
--   type variables.
simplifyTypedExpr (HS.Con _ conName) resType =
  addTypeEquationFor conName resType
simplifyTypedExpr (HS.Var _ varName) resType = ifM
  (lift $ inEnv $ isFunction varName)
  (addTypeEquationFor varName resType)
  (addVarType varName resType)

-- If @(e₁ e₂) :: τ@, then @e₁ :: α -> τ@ and @e₂ :: α@ where @α@ is a new
-- type variable.
simplifyTypedExpr (HS.App _ e1 e2) resType = do
  argType <- lift freshTypeVar
  simplifyTypedExpr e1 (HS.TypeFunc NoSrcSpan argType resType)
  simplifyTypedExpr e2 argType

-- If @if e₁ then e₂ else e₃ :: τ@, then @e₁ :: Bool@ and @e₂, e₃ :: τ@.
simplifyTypedExpr (HS.If _ e1 e2 e3) resType = do
  let condType = HS.TypeCon NoSrcSpan HS.boolTypeConName
  simplifyTypedExpr e1 condType
  simplifyTypedExpr e2 resType
  simplifyTypedExpr e3 resType

-- If @case e of {p₀ -> e₀; …; pₙ -> eₙ} :: τ@, then @e₀, …, eₙ :: τ@ and
-- @e :: α@ and @p₀, …, pₙ :: α@ where @α@ is a new type variable.
simplifyTypedExpr (HS.Case _ expr alts) resType = do
  exprType <- lift freshTypeVar
  simplifyTypedExpr expr exprType
  mapM_ (\alt -> simplifyTypedAlt alt exprType resType) alts

-- Error terms are always typed correctly.
simplifyTypedExpr (HS.Undefined _   ) _       = return ()
simplifyTypedExpr (HS.ErrorExpr  _ _) _       = return ()

-- If @n :: τ@ for some integer literal @n@, then @τ = Integer@.
simplifyTypedExpr (HS.IntLiteral _ _) resType = do
  addTypeEquation resType (HS.TypeCon NoSrcSpan HS.integerTypeConName)

-- If @\x₀ … xₙ -> e :: τ@, then @x₀ :: α₀, … xₙ :: αₙ@ and @x :: β@ for new
-- type variables @α₀ … αₙ@ and @α₀ -> … -> αₙ -> β = τ@.
simplifyTypedExpr (HS.Lambda _ args expr) resType = do
  argTypes   <- mapM (const (lift freshTypeVar)) args
  returnType <- lift freshTypeVar
  zipWithM_ simplifyTypedExpr (map HS.varPatToExpr args) argTypes
  simplifyTypedExpr expr returnType
  let funcType = HS.funcType NoSrcSpan argTypes returnType
  addTypeEquation funcType resType

-- If @(e :: forall α₀, …, αₙ. τ) :: τ'@, then @e :: σ(τ)@ and @σ(τ) = τ'@
-- where @σ = { α₀ ↦ β₀, …, αₙ ↦ βₙ }@ maps the quantified type variables
-- of @τ@ to new type variables @β₀, …, βₙ@.
simplifyTypedExpr (HS.ExprTypeSig _ expr typeSchema) resType = do
  exprType <- lift $ instantiateTypeSchema typeSchema
  simplifyTypedExpr expr exprType
  addTypeEquation exprType resType

-- | Applies 'simplifyTypedExpr' to the pattern and right-hand side of a
--   @case@-expression alternative.
simplifyTypedAlt
  :: HS.Alt  -- ^ The @case@-expression alternative.
  -> HS.Type -- ^ The type of the pattern.
  -> HS.Type -- ^ The type of the right-hand side.
  -> TypedExprSimplifier ()
simplifyTypedAlt (HS.Alt _ conPat varPats expr) patType exprType = do
  let pat =
        HS.app NoSrcSpan (HS.conPatToExpr conPat) (map HS.varPatToExpr varPats)
  simplifyTypedExpr pat  patType
  simplifyTypedExpr expr exprType

-------------------------------------------------------------------------------
-- Solving type equations                                                    --
-------------------------------------------------------------------------------

-- | Converts @n@ 'TypedVar' entries for the same variable to @n-1@
--   type equations.
makeTypeEquations :: [TypedVar] -> [TypeEquation]
makeTypeEquations []                     = []
makeTypeEquations ((var, typeExpr) : ps) = case lookup var ps of
  Nothing        -> makeTypeEquations ps
  Just typeExpr' -> (typeExpr, typeExpr') : makeTypeEquations ps

-- | Finds the most general unificator that satisfies all given type equations.
unifyEquations :: [TypeEquation] -> Converter (Subst HS.Type)
unifyEquations = unifyEquations' identitySubst
 where
  unifyEquations'
    :: Subst HS.Type -> [TypeEquation] -> Converter (Subst HS.Type)
  unifyEquations' subst []                = return subst
  unifyEquations' subst ((t1, t2) : eqns) = do
    t1' <- applySubst subst t1
    t2' <- applySubst subst t2
    mgu <- unify t1' t2'
    unifyEquations' (composeSubst subst mgu) eqns

-------------------------------------------------------------------------------
-- Type schemas                                                              --
-------------------------------------------------------------------------------

-- | Replaces the type variables in the given type schema by fresh type
--   variables.
instantiateTypeSchema :: HS.TypeSchema -> Converter HS.Type
instantiateTypeSchema (HS.TypeSchema _ typeArgs typeExpr) = do
  typeArgs' <- mapM (const freshTypeVar) typeArgs
  let names = map (HS.UnQual . HS.Ident . HS.fromDeclIdent) typeArgs
      subst = composeSubsts (zipWith singleSubst names typeArgs')
  applySubst subst typeExpr

-- | Normalizes the names of type variables in the given type and returns
--   it as a type schema.
abstractTypeSchema :: HS.Type -> Converter HS.TypeSchema
abstractTypeSchema t = do
  let vs    = typeVars t
      vs'   = map ((freshTypeVarPrefix ++) . show) [0 .. length vs - 1]
      ts    = map (HS.TypeVar NoSrcSpan) vs'
      subst = composeSubsts (zipWith singleSubst vs ts)
  t' <- applySubst subst t
  return (HS.TypeSchema NoSrcSpan (map (HS.DeclIdent NoSrcSpan) vs') t')
