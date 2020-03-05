-- | This module contains functions for infering the type of expressions
--   and function declarations as well as functions for annotating the types
--   of variable patterns and adding visible applications for type arguments.

module Compiler.Analysis.TypeInference
  ( -- * Function declarations
    inferFuncDeclTypes
  , annotateFuncDeclTypes
  , annotateFuncDeclTypes'
    -- * Expressions
  , inferExprType
  , annotateExprTypes
  , annotateExprTypes'
  )
where

import           Control.Monad.Extra            ( mapAndUnzipM
                                                , replicateM
                                                )
import           Control.Monad.Writer
import           Control.Monad.Reader
import           Data.Composition               ( (.:) )
import           Data.List                      ( (\\)
                                                , nub
                                                , partition
                                                )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromJust
                                                , maybeToList
                                                )

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
import           Compiler.Monad.Reporter

-- | Maps the names of defined functions and constructors to their type schema.
type TypeAssumption = Map HS.QName HS.TypeSchema

-- | Creates a 'TypeAssumption' for all funtions and constructors defined
--   in the given environment.
makeTypeAssumtion :: Environment -> TypeAssumption
makeTypeAssumtion env = entryTypeAssumtion `Map.union` typeSigTypeAssumtion
 where
  entryTypeAssumtion, typeSigTypeAssumtion :: TypeAssumption
  entryTypeAssumtion = Map.fromList
    [ (name, typeSchema)
    | (scope, name) <- Map.keys (envEntries env)
    , scope == ValueScope
    , typeSchema <- maybeToList (lookupTypeSchema scope name env)
    ]
  typeSigTypeAssumtion = envTypeSigs env

-- | Remoes all variables bound by the given variable patterns from the given
--   type assumption.
removeVarPatsFromTypeAssumption
  :: [HS.VarPat] -> TypeAssumption -> TypeAssumption
removeVarPatsFromTypeAssumption = flip (foldr removeVarPatFromTypeAssumption)

-- | Removes the variable bound by the given variable pattern from the given
--   type assumption.
removeVarPatFromTypeAssumption :: HS.VarPat -> TypeAssumption -> TypeAssumption
removeVarPatFromTypeAssumption (HS.VarPat _ ident _) ta =
  let name = HS.UnQual (HS.Ident ident) in Map.delete name ta

-- | Adds the type schemas for the given function and constructor names to
--   the given type assumption.
extendTypeAssumption
  :: [(HS.QName, HS.TypeSchema)] -> TypeAssumption -> TypeAssumption
extendTypeAssumption ps ta = Map.fromList ps `Map.union` ta

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Tries to infer the types of (mutually recursive) function declarations.
inferFuncDeclTypes :: [HS.FuncDecl] -> Converter [HS.TypeSchema]
inferFuncDeclTypes = fmap snd . annotateFuncDeclTypes'

-- | Like 'inferFuncDeclTypes' but does not abstract the type to a type
--   schema and returns the substitution.
inferFuncDeclTypes'
  :: [HS.FuncDecl] -> TypeAssumption -> Converter ([HS.Type], Subst HS.Type)
inferFuncDeclTypes' funcDecls ta = localEnv $ do
  (typedExprs, funcTypes) <- mapAndUnzipM makeTypedExprs funcDecls
  eqns                    <- execTypedExprSimplifier ta $ do
    zipWithM_ addTypeSigEquation funcDecls funcTypes
    mapM_ (uncurry simplifyTypedExpr) (concat typedExprs)
  mgu        <- unifyEquations eqns
  funcTypes' <- mapM (applySubst mgu) funcTypes
  return (funcTypes', mgu)

-- | Creates fresh type variables @a@ and @a1 ... an@ and the expression/type
--   pairs @f :: a1 -> ... -> an -> a, x1 :: a1, ..., xn :: an@ and @e :: a@
--   for the given function declaration @f x1 ... xn = e@ and returns the
--   expression/type pairs as well as the type of the function.
makeTypedExprs :: HS.FuncDecl -> Converter ([(HS.Expr, HS.Type)], HS.Type)
makeTypedExprs (HS.FuncDecl _ (HS.DeclIdent srcSpan ident) args rhs) = do
  (args', rhs') <- renameArgs args rhs
  argTypeVars   <- mapM makeArgTypeVar args
  resTypeVar    <- freshTypeVar
  let funcName = HS.UnQual (HS.Ident ident)
      funcExpr = HS.Var srcSpan funcName
      funcType = HS.funcType NoSrcSpan argTypeVars resTypeVar
      argExprs = map HS.varPatToExpr args'
      typedExprs =
        (funcExpr, funcType) : (rhs', resTypeVar) : zip argExprs argTypeVars
  return (typedExprs, funcType)
 where
  -- | Generates a fresh type variable for the given variable pattern or
  --   returns the type variable generated by 'annotateFuncDecl'.
  makeArgTypeVar :: HS.VarPat -> Converter HS.Type
  makeArgTypeVar (HS.VarPat _ _ Nothing       ) = freshTypeVar
  makeArgTypeVar (HS.VarPat _ _ (Just varType)) = return varType

-- If the given function has a type signature @f :: τ@ and 'makeTypedExprs'
-- added the expression type pair @f :: τ'@, the type equation @τ = τ'@ is
-- added without instantiating the type variables in the type signature with
-- fresh identifiers such that the inferred type uses the same type variable
-- names as specified by the user.
addTypeSigEquation :: HS.FuncDecl -> HS.Type -> TypedExprSimplifier ()
addTypeSigEquation funcDecl funcType = do
  let funcIdent = HS.fromDeclIdent (HS.getDeclIdent funcDecl)
      funcName  = HS.UnQual (HS.Ident funcIdent)
  maybeTypeSig <- liftConverter $ inEnv $ lookupTypeSig funcName
  mapM_
    (\(HS.TypeSchema srcSpan _ typeSig) ->
      addTypeEquation srcSpan typeSig funcType
    )
    maybeTypeSig

-- | Infers the types of type arguments to functions and constructors
--   used by the right-hand side of the given function declaration.
annotateFuncDeclTypes :: [HS.FuncDecl] -> Converter [HS.FuncDecl]
annotateFuncDeclTypes = fmap fst . annotateFuncDeclTypes'

-- | Like 'annotateFuncDeclTypes' but also returns the type of the
--   function declaration.
annotateFuncDeclTypes'
  :: [HS.FuncDecl] -> Converter ([HS.FuncDecl], [HS.TypeSchema])
annotateFuncDeclTypes' funcDecls = localEnv $ do
  -- Add type annotations.
  annotatedFuncDecls <- mapM annotateFuncDecl funcDecls
  -- Infer function types.
  ta                 <- inEnv makeTypeAssumtion
  (typeExprs, mgu)   <- inferFuncDeclTypes' annotatedFuncDecls ta
  typedFuncDecls     <- mapM (applySubst mgu) annotatedFuncDecls
  -- Abstract inferred type schema.
  let typeArgs           = map typeVars typeExprs
      additionalTypeArgs = map typeVars typedFuncDecls
      allTypeArgs        = zipWith (nub .: (++)) typeArgs additionalTypeArgs
  (typeSchemas, substs) <-
    unzip <$> zipWithM abstractTypeSchema' allTypeArgs typeExprs
  abstractedFuncDecls <- zipWithM applySubst substs typedFuncDecls
  -- Add visible type applications.
  modName             <- inEnv envModName
  let funcIdents      = map (HS.fromDeclIdent . HS.getDeclIdent) funcDecls
      funcUnqualNames = map (HS.UnQual . HS.Ident) funcIdents
      funcQualNames   = map (HS.Qual modName . HS.Ident) funcIdents
      ta'             = extendTypeAssumption
        (zip funcUnqualNames typeSchemas ++ zip funcQualNames typeSchemas)
        ta
  funcDecls' <- mapM (addTypeAppExprsToFuncDecl ta') abstractedFuncDecls
  return (funcDecls', typeSchemas)

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Tries to infer the type of the given expression from the current context
--   and abstracts it's type to a type schema.
inferExprType :: HS.Expr -> Converter HS.TypeSchema
inferExprType = fmap snd . annotateExprTypes'

-- | Like 'inferExprType' but does not abstract the type to a type schema and
--   also returns the substitution.
inferExprType'
  :: HS.Expr -> TypeAssumption -> Converter (HS.Type, Subst HS.Type)
inferExprType' expr ta = localEnv $ do
  typeVar  <- freshTypeVar
  eqns     <- execTypedExprSimplifier ta $ simplifyTypedExpr expr typeVar
  mgu      <- unifyEquations eqns
  exprType <- applySubst mgu typeVar
  return (exprType, mgu)

-- | Infers the types of type arguments to functions and constructors
--   used by the given expression.
--
--   Returns an expression where the type arguments of functions and
--   constructors are applied explicitly.
annotateExprTypes :: HS.Expr -> Converter HS.Expr
annotateExprTypes = fmap fst . annotateExprTypes'

-- | Like 'annotateExprTypes' but also returns the type of the expression.
annotateExprTypes' :: HS.Expr -> Converter (HS.Expr, HS.TypeSchema)
annotateExprTypes' expr = localEnv $ do
  -- Add type annotations.
  annotatedExpr   <- annotateExpr expr
  -- Infer type.
  ta              <- inEnv makeTypeAssumtion
  (typeExpr, mgu) <- inferExprType' annotatedExpr ta
  typedExpr       <- applySubst mgu annotatedExpr
  -- Abstract inferred type schema.
  let typeArgs = nub (typeVars typedExpr ++ typeVars typeExpr)
  (typeSchema, subst) <- abstractTypeSchema' typeArgs typeExpr
  abstractedExpr      <- applySubst subst typedExpr
  -- Add visible type applications.
  expr'               <- addTypeAppExprs ta abstractedExpr
  return (expr', typeSchema)

-------------------------------------------------------------------------------
-- Type annotations                                                          --
-------------------------------------------------------------------------------

-- | Annotates the type of the given variable pattern using a fresh type
--   variable.
--
--   Exisiting type annotations are discarded.
annotateVarPat :: HS.VarPat -> Converter HS.VarPat
annotateVarPat (HS.VarPat srcSpan ident _) = do
  typeVar <- freshTypeVar
  return (HS.VarPat srcSpan ident (Just typeVar))

-- | Annotates the given expression (a constructor or function application
--   or an error term) using a type signature and fresh type variable.
annotateWithTypeSig :: HS.Expr -> Converter HS.Expr
annotateWithTypeSig expr = do
  typeVar <- freshTypeVar
  let srcSpan = HS.getSrcSpan expr
  return (HS.ExprTypeSig srcSpan expr (HS.TypeSchema srcSpan [] typeVar))

-- | Adds fresh type variables to variable patterns in the given expression
--   and adds type signatures to constructor and function invocations as well
--   as error terms.
--
--   The fresh type variables are later replaced by the actual type
--   using the substitution computed during type inference.
annotateExpr :: HS.Expr -> Converter HS.Expr

-- Add type annotation to constructor and function invocations.
annotateExpr expr@(HS.Con _ _                  ) = annotateWithTypeSig expr
annotateExpr expr@(HS.Var _ _                  ) = annotateWithTypeSig expr

-- Add type annotation to error terms.
annotateExpr expr@(HS.Undefined _              ) = annotateWithTypeSig expr
annotateExpr expr@(HS.ErrorExpr _ _            ) = annotateWithTypeSig expr

-- There should be no visible type applications prior to type inference.
annotateExpr (     HS.TypeAppExpr srcSpan _  _ ) = unexpectedTypeAppExpr srcSpan

-- Add visible type applications recursively.
annotateExpr (     HS.App         srcSpan e1 e2) = do
  e1' <- annotateExpr e1
  e2' <- annotateExpr e2
  return (HS.App srcSpan e1' e2')
annotateExpr (HS.If srcSpan e1 e2 e3) = do
  e1' <- annotateExpr e1
  e2' <- annotateExpr e2
  e3' <- annotateExpr e3
  return (HS.If srcSpan e1' e2' e3')
annotateExpr (HS.Case srcSpan expr alts) = do
  expr' <- annotateExpr expr
  alts' <- mapM annotateAlt alts
  return (HS.Case srcSpan expr' alts')
annotateExpr (HS.Lambda srcSpan varPats expr) = do
  varPats' <- mapM annotateVarPat varPats
  expr'    <- annotateExpr expr
  return (HS.Lambda srcSpan varPats' expr')
annotateExpr (HS.ExprTypeSig srcSpan expr typeSchema) = do
  expr' <- annotateExpr expr
  return (HS.ExprTypeSig srcSpan expr' typeSchema)
annotateExpr expr@(HS.IntLiteral _ _) = return expr

-- | Applies 'annotateExpr' to the right-hand side of an alternative
--   of  a @case@-expression and annotates the variable patterns with
--   fresh type variable.
annotateAlt :: HS.Alt -> Converter HS.Alt
annotateAlt (HS.Alt srcSpan conPat varPats expr) = do
  varPats' <- mapM annotateVarPat varPats
  expr'    <- annotateExpr expr
  return (HS.Alt srcSpan conPat varPats' expr')

-- | Applies 'annotateExpr' to the right-hand side of a function
--   declaration and annotates the function arguments with fresh type
--   variables.
annotateFuncDecl :: HS.FuncDecl -> Converter HS.FuncDecl
annotateFuncDecl (HS.FuncDecl srcSpan declIdent args rhs) = do
  args' <- mapM annotateVarPat args
  rhs'  <- annotateExpr rhs
  return (HS.FuncDecl srcSpan declIdent args' rhs')

-------------------------------------------------------------------------------
-- Visible type application                                                  --
-------------------------------------------------------------------------------

-- | Replaces a type signature added by 'annotateExpr' for a variable or
--   constructor with the given name by a visible type application of that
--   function or constructor.
addTypeAppExprsFor
  :: TypeAssumption -> HS.QName -> HS.Expr -> HS.Type -> Converter HS.Expr
addTypeAppExprsFor ta name expr typeExpr = case Map.lookup name ta of
  Nothing         -> return expr
  Just typeSchema -> do
    let srcSpan = HS.getSrcSpan expr
    (typeExpr', typeArgs) <- instantiateTypeSchema' typeSchema
    mgu                   <- unifyOrFail srcSpan typeExpr typeExpr'
    typeArgs'             <- mapM (applySubst mgu) typeArgs
    return (HS.visibleTypeApp srcSpan expr typeArgs')

-- | Replaces the type signatures added by 'annotateExpr' by visible type
--   application expressions.
addTypeAppExprs :: TypeAssumption -> HS.Expr -> Converter HS.Expr

-- Add visible type applications to functions and constructors.
addTypeAppExprs ta (HS.ExprTypeSig _ expr@(HS.Con _ conName) (HS.TypeSchema _ [] typeExpr))
  = addTypeAppExprsFor ta conName expr typeExpr
addTypeAppExprs ta (HS.ExprTypeSig _ expr@(HS.Var _ varName) (HS.TypeSchema _ [] typeExpr))
  = addTypeAppExprsFor ta varName expr typeExpr

-- Add visible type applications to error terms.
addTypeAppExprs _ (HS.ExprTypeSig srcSpan expr@(HS.Undefined _) (HS.TypeSchema _ [] typeExpr))
  = return (HS.TypeAppExpr srcSpan expr typeExpr)
addTypeAppExprs _ (HS.ExprTypeSig srcSpan expr@(HS.ErrorExpr _ _) (HS.TypeSchema _ [] typeExpr))
  = return (HS.TypeAppExpr srcSpan expr typeExpr)

-- There should be no visible type applications prior to type inference.
addTypeAppExprs _ (HS.TypeAppExpr srcSpan _ _) = unexpectedTypeAppExpr srcSpan

-- Recursively add visible type applications.
addTypeAppExprs ta (HS.ExprTypeSig srcSpan expr typeSchema) = do
  expr' <- addTypeAppExprs ta expr
  return (HS.ExprTypeSig srcSpan expr' typeSchema)
addTypeAppExprs ta (HS.App srcSpan e1 e2) = do
  e1' <- addTypeAppExprs ta e1
  e2' <- addTypeAppExprs ta e2
  return (HS.App srcSpan e1' e2')
addTypeAppExprs ta (HS.If srcSpan e1 e2 e3) = do
  e1' <- addTypeAppExprs ta e1
  e2' <- addTypeAppExprs ta e2
  e3' <- addTypeAppExprs ta e3
  return (HS.If srcSpan e1' e2' e3')
addTypeAppExprs ta (HS.Case srcSpan expr alts) = do
  expr' <- addTypeAppExprs ta expr
  alts' <- mapM (addTypeAppExprsToAlt ta) alts
  return (HS.Case srcSpan expr' alts')
addTypeAppExprs ta (HS.Lambda srcSpan args expr) = do
  let ta' = removeVarPatsFromTypeAssumption args ta
  expr' <- addTypeAppExprs ta' expr
  return (HS.Lambda srcSpan args expr')

-- Leave all other expressions unchanged.
addTypeAppExprs _ expr@(HS.Con _ _       ) = return expr
addTypeAppExprs _ expr@(HS.Var _ _       ) = return expr
addTypeAppExprs _ expr@(HS.Undefined _   ) = return expr
addTypeAppExprs _ expr@(HS.ErrorExpr  _ _) = return expr
addTypeAppExprs _ expr@(HS.IntLiteral _ _) = return expr

-- | Applies 'addTypeAppExprs' to the right-hand side of the given @case@-
--   expression alternative.
addTypeAppExprsToAlt :: TypeAssumption -> HS.Alt -> Converter HS.Alt
addTypeAppExprsToAlt ta (HS.Alt srcSpan conPat varPats expr) = do
  let ta' = removeVarPatsFromTypeAssumption varPats ta
  expr' <- addTypeAppExprs ta' expr
  return (HS.Alt srcSpan conPat varPats expr')

-- | Applies ' addTypeAppExprs' to the right-hand side of the given function
--   declaration.
addTypeAppExprsToFuncDecl
  :: TypeAssumption -> HS.FuncDecl -> Converter HS.FuncDecl
addTypeAppExprsToFuncDecl ta (HS.FuncDecl srcSpan declIdent args rhs) = do
  let ta' = removeVarPatsFromTypeAssumption args ta
  rhs' <- addTypeAppExprs ta' rhs
  return (HS.FuncDecl srcSpan declIdent args rhs')

-------------------------------------------------------------------------------
-- Simplification of expression/type pairs                                   --
-------------------------------------------------------------------------------

-- | A pair of a variable name and its expected type type and location in the
--   source code.
type TypedVar = (HS.VarName, (SrcSpan, HS.Type))

-- | A type equation and the location in the source that caused the creation
--   of this type variable.
type TypeEquation = (SrcSpan, HS.Type, HS.Type)

-- | A writer monad that allows 'simplifyTypedExpr' to generate 'TypedVar's
--   and 'TypeEquation's implicitly.
type TypedExprSimplifier a =
  WriterT ([TypedVar], [TypeEquation]) (ReaderT TypeAssumption Converter) a

instance (MonadConverter m, Monoid w) => MonadConverter (WriterT w m) where
  liftConverter = lift . liftConverter

instance MonadConverter m => MonadConverter (ReaderT r m) where
  liftConverter = lift . liftConverter

-- | Gets the type assumption.
getTypeAssumption :: TypedExprSimplifier TypeAssumption
getTypeAssumption = lift ask

-- | Runs the given simplifier for expression/type pairs and returns the
--   yielded type equations (including type equations for variable/type pairs
--   with the same name, see 'makeTypeEquations') in addition to the
--   simplifiers result.
runTypedExprSimplifier
  :: TypeAssumption -> TypedExprSimplifier a -> Converter (a, [TypeEquation])
runTypedExprSimplifier ta mx = do
  (x, (varTypes, eqns)) <- runReaderT (runWriterT mx) ta
  let eqns' = makeTypeEquations varTypes ++ eqns
  return (x, eqns')

-- | Like 'runTypedExprSimplifier' but discards the result.
execTypedExprSimplifier
  :: TypeAssumption -> TypedExprSimplifier a -> Converter [TypeEquation]
execTypedExprSimplifier = fmap snd .: runTypedExprSimplifier

-- | Adds a 'TypedVar' entry to a 'TypedExprSimplifier'.
addVarType :: SrcSpan -> HS.QName -> HS.Type -> TypedExprSimplifier ()
addVarType srcSpan v t = tell ([(v, (srcSpan, t))], [])

-- | Adds a 'TypeEquation' entry to a 'TypedExprSimplifier'.
addTypeEquation :: SrcSpan -> HS.Type -> HS.Type -> TypedExprSimplifier ()
addTypeEquation srcSpan t t' = tell ([], [(srcSpan, t, t')])

-- | Instantiates the type schema of the function or constructor with the
--   given name and adds a 'TypeEquation' for the resulting type and the
--   given type.
--
--   If there is no entry for the given name, a fatal error is reported.
--   The error message refers to the given source location information.
addTypeEquationOrVarTypeFor
  :: SrcSpan -> HS.QName -> HS.Type -> TypedExprSimplifier ()
addTypeEquationOrVarTypeFor srcSpan name resType = do
  ta <- getTypeAssumption
  case Map.lookup name ta of
    Nothing         -> addVarType srcSpan name resType
    Just typeSchema -> do
      funcType <- liftConverter $ instantiateTypeSchema typeSchema
      addTypeEquation srcSpan funcType resType

-- | Simplifies expression/type pairs to variables/type pairs and type
--   equations.
simplifyTypedExpr :: HS.Expr -> HS.Type -> TypedExprSimplifier ()

-- | If @C :: τ@ is a predefined constructor with @C :: forall α₀ … αₙ. τ'@,
--   then @τ = σ(τ')@ with @σ = { α₀ ↦ β₀, …, αₙ ↦ βₙ }@ where @β₀, …, βₙ@ are
--   new type variables.
simplifyTypedExpr (HS.Con srcSpan conName) resType =
  addTypeEquationOrVarTypeFor srcSpan conName resType

-- | If @f :: τ@ is a predefined function with @f :: forall α₀ … αₙ. τ'@, then
--   @τ = σ(τ')@ with @σ = { α₀ ↦ β₀, …, αₙ ↦ βₙ }@ where @β₀, …, βₙ@ are new
--   type variables.
--   If @x :: τ@ is not a predefined function (i.e., a local variable or a
--   function whose type to infer), just remember that @x@ is of type @τ@.
simplifyTypedExpr (HS.Var srcSpan varName) resType =
  addTypeEquationOrVarTypeFor srcSpan varName resType

-- If @(e₁ e₂) :: τ@, then @e₁ :: α -> τ@ and @e₂ :: α@ where @α@ is a new
-- type variable.
simplifyTypedExpr (HS.App _ e1 e2) resType = do
  argType <- liftConverter freshTypeVar
  simplifyTypedExpr e1 (HS.TypeFunc NoSrcSpan argType resType)
  simplifyTypedExpr e2 argType

-- There should be no visible type applications prior to type inference.
simplifyTypedExpr (HS.TypeAppExpr srcSpan _ _) _ =
  liftConverter $ unexpectedTypeAppExpr srcSpan

-- If @if e₁ then e₂ else e₃ :: τ@, then @e₁ :: Bool@ and @e₂, e₃ :: τ@.
simplifyTypedExpr (HS.If _ e1 e2 e3) resType = do
  let condType = HS.TypeCon NoSrcSpan HS.boolTypeConName
  simplifyTypedExpr e1 condType
  simplifyTypedExpr e2 resType
  simplifyTypedExpr e3 resType

-- If @case e of {p₀ -> e₀; …; pₙ -> eₙ} :: τ@, then @e₀, …, eₙ :: τ@ and
-- @e :: α@ and @p₀, …, pₙ :: α@ where @α@ is a new type variable.
simplifyTypedExpr (HS.Case _ expr alts) resType = do
  exprType <- liftConverter freshTypeVar
  simplifyTypedExpr expr exprType
  mapM_ (\alt -> simplifyTypedAlt alt exprType resType) alts

-- Error terms are always typed correctly.
simplifyTypedExpr (HS.Undefined _  ) _ = return ()
simplifyTypedExpr (HS.ErrorExpr _ _) _ = return ()

-- If @n :: τ@ for some integer literal @n@, then @τ = Integer@.
simplifyTypedExpr (HS.IntLiteral srcSpan _) resType =
  addTypeEquation srcSpan (HS.TypeCon NoSrcSpan HS.integerTypeConName) resType

-- If @\x₀ … xₙ -> e :: τ@, then @x₀ :: α₀, … xₙ :: αₙ@ and @x :: β@ for new
-- type variables @α₀ … αₙ@ and @α₀ -> … -> αₙ -> β = τ@.
simplifyTypedExpr (HS.Lambda srcSpan args expr) resType = do
  (args', expr') <- liftConverter $ renameArgs args expr
  argTypes       <- replicateM (length args') (liftConverter freshTypeVar)
  returnType     <- liftConverter freshTypeVar
  zipWithM_ simplifyTypedVarPat args' argTypes
  simplifyTypedExpr expr' returnType
  let funcType = HS.funcType NoSrcSpan argTypes returnType
  addTypeEquation srcSpan funcType resType

-- If @(e :: forall α₀, …, αₙ. τ) :: τ'@, then @e :: σ(τ)@ and @σ(τ) = τ'@
-- where @σ = { α₀ ↦ β₀, …, αₙ ↦ βₙ }@ maps the quantified type variables
-- of @τ@ to new type variables @β₀, …, βₙ@.
simplifyTypedExpr (HS.ExprTypeSig srcSpan expr typeSchema) resType = do
  exprType <- liftConverter $ instantiateTypeSchema typeSchema
  simplifyTypedExpr expr exprType
  addTypeEquation srcSpan exprType resType

-- | Applies 'simplifyTypedExpr' to the pattern and right-hand side of a
--   @case@-expression alternative.
simplifyTypedAlt
  :: HS.Alt  -- ^ The @case@-expression alternative.
  -> HS.Type -- ^ The type of the pattern.
  -> HS.Type -- ^ The type of the right-hand side.
  -> TypedExprSimplifier ()
simplifyTypedAlt (HS.Alt _ conPat varPats expr) patType exprType = do
  (varPats', expr') <- liftConverter $ renameArgs varPats expr
  simplifyTypedPat conPat varPats' patType
  simplifyTypedExpr expr' exprType

-- | Applies 'simplifyTypedConPat' to the given constructor pattern and
--   'simplifyTypedVarPat' to the given variable patterns.
simplifyTypedPat
  :: HS.ConPat -> [HS.VarPat] -> HS.Type -> TypedExprSimplifier ()
simplifyTypedPat conPat varPats patType = do
  varPatTypes <- liftConverter $ replicateM (length varPats) freshTypeVar
  let conPatType = HS.funcType NoSrcSpan varPatTypes patType
  simplifyTypedConPat conPat conPatType
  zipWithM_ simplifyTypedVarPat varPats varPatTypes

-- | Adds a type equation for the given constructor pattern that unifies the
--   given type with an instance of the constructor's type schema.
simplifyTypedConPat :: HS.ConPat -> HS.Type -> TypedExprSimplifier ()
simplifyTypedConPat (HS.ConPat srcSpan conName) conPatType =
  addTypeEquationOrVarTypeFor srcSpan conName conPatType

-- | Adds two 'TypedVar' entries for the given variable pattern. One for
--   the given and one for the annotated type.
simplifyTypedVarPat :: HS.VarPat -> HS.Type -> TypedExprSimplifier ()
simplifyTypedVarPat (HS.VarPat srcSpan varIdent maybeVarType) varPatType = do
  let varName = HS.UnQual (HS.Ident varIdent)
  addVarType srcSpan varName varPatType
  mapM_ (addVarType srcSpan varName) maybeVarType

-------------------------------------------------------------------------------
-- Solving type equations                                                    --
-------------------------------------------------------------------------------

-- | Converts @n@ 'TypedVar' entries for the same variable to @n-1@
--   type equations.
makeTypeEquations :: [TypedVar] -> [TypeEquation]
makeTypeEquations [] = []
makeTypeEquations ((var, (srcSpan, typeExpr)) : ps) = case lookup var ps of
  Nothing             -> makeTypeEquations ps
  Just (_, typeExpr') -> (srcSpan, typeExpr, typeExpr') : makeTypeEquations ps

-- | Finds the most general unificator that satisfies all given type equations.
unifyEquations :: [TypeEquation] -> Converter (Subst HS.Type)
unifyEquations = unifyEquations' identitySubst
 where
  unifyEquations'
    :: Subst HS.Type -> [TypeEquation] -> Converter (Subst HS.Type)
  unifyEquations' subst []                         = return subst
  unifyEquations' subst ((srcSpan, t1, t2) : eqns) = do
    t1' <- applySubst subst t1
    t2' <- applySubst subst t2
    mgu <- unifyOrFail srcSpan t1' t2'
    let subst' = composeSubst mgu subst
    unifyEquations' subst' eqns

-------------------------------------------------------------------------------
-- Type schemas                                                              --
-------------------------------------------------------------------------------

-- | Replaces the type variables in the given type schema by fresh type
--   variables.
instantiateTypeSchema :: HS.TypeSchema -> Converter HS.Type
instantiateTypeSchema = fmap fst . instantiateTypeSchema'

-- | Like 'instantiateTypeSchema'' but also returns the fresh type variables,
--   the type schema has been instantiated with.
instantiateTypeSchema' :: HS.TypeSchema -> Converter (HS.Type, [HS.Type])
instantiateTypeSchema' (HS.TypeSchema _ typeArgs typeExpr) = do
  let typeArgIdents = map HS.fromDeclIdent typeArgs
  (typeArgIdents', subst) <- renameTypeArgsSubst typeArgIdents
  typeExpr'               <- applySubst subst typeExpr
  let typeArgs' = map (HS.TypeVar NoSrcSpan) typeArgIdents'
  return (typeExpr', typeArgs')

-- | Normalizes the names of type variables in the given type and returns
--   it as a type schema.
--
--   The first argument contains the names of type variables that should be
--   bound by the type schema. Usually these are the type variables that
--   occur in the given type (see 'typeVars').
--
--   Fresh type variables used by the given type are replaced by regular type
--   varibales with the prefix 'freshTypeArgPrefix'. All other type variables
--   are not renamed.
abstractTypeSchema :: [HS.QName] -> HS.Type -> Converter HS.TypeSchema
abstractTypeSchema = fmap fst .: abstractTypeSchema'

-- | Like 'abstractTypeSchema' but also returns the substitution that
--   was applied to replace the type variables.
abstractTypeSchema'
  :: [HS.QName] -> HS.Type -> Converter (HS.TypeSchema, Subst HS.Type)
abstractTypeSchema' ns t = do
  let vs         = map (fromJust . HS.identFromQName) ns
      (ivs, uvs) = partition HS.isInternalIdent vs
      vs'        = uvs ++ take (length ivs) (map makeTypeArg [0 ..] \\ uvs)
      ns'        = map (HS.UnQual . HS.Ident) (uvs ++ ivs)
      ts         = map (HS.TypeVar NoSrcSpan) vs'
      subst      = composeSubsts (zipWith singleSubst ns' ts)
  t' <- applySubst subst t
  return (HS.TypeSchema NoSrcSpan (map (HS.DeclIdent NoSrcSpan) vs') t', subst)
 where
  makeTypeArg :: Int -> HS.TypeVarIdent
  makeTypeArg = (freshTypeArgPrefix ++) . show

-------------------------------------------------------------------------------
-- Error reporting                                                           --
-------------------------------------------------------------------------------

-- | Reports an internal error when a type application expression is
--   encountered prior to type inference.
unexpectedTypeAppExpr :: MonadReporter r => SrcSpan -> r a
unexpectedTypeAppExpr srcSpan =
  reportFatal
    $ Message srcSpan Internal
    $ "Unexpected visible type application."
