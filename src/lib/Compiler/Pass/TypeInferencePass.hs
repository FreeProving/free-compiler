{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | This module contains a compiler pass that infers the types of all
--   function declarations including the types of the sub-expressions of
--   their right-hand sides and type arguments to pass to used functions and
--   constructors.
--
--   TODO write documentation and examples

module Compiler.Pass.TypeInferencePass
  ( typeInferencePass
  )
where

import           Control.Monad.Fail             ( MonadFail )
import           Control.Monad.Extra            ( zipWithM
                                                , zipWithM_
                                                )
import           Control.Monad.State            ( MonadState(..)
                                                , StateT(..)
                                                , evalStateT
                                                , gets
                                                , modify
                                                )
import           Data.Composition               ( (.:) )
import           Data.List                      ( (\\)
                                                , nub
                                                )
import           Data.List.Extra                ( dropEnd
                                                , takeEnd
                                                )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromJust
                                                , maybeToList
                                                )
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyExtraction
                                                ( typeVars )
import           Compiler.Backend.Coq.Converter.TypeSchema
import           Compiler.Environment
import           Compiler.Environment.Fresh
import           Compiler.Environment.Scope
import           Compiler.IR.SrcSpan
import           Compiler.IR.Subst
import qualified Compiler.IR.Syntax            as HS
import           Compiler.IR.Unification
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pass.DependencyAnalysisPass
import           Compiler.Pretty

-- | A compiler pass that infers the types of (mutually recursive) function
--   declarations in the given strongly connected component of the function
--   dependency graph.
typeInferencePass :: DependencyAwarePass HS.FuncDecl
typeInferencePass = mapComponentM inferFuncDeclTypes

-------------------------------------------------------------------------------
-- Type inference state monad                                                --
-------------------------------------------------------------------------------

-- | A type equation and the location in the source that caused the creation
--   of this type variable.
type TypeEquation = (SrcSpan, HS.Type, HS.Type)

-- | Maps the names of defined functions and constructors to their type schema.
type TypeAssumption = Map HS.QName HS.TypeSchema

-- | The state that is passed implicitly between the modules of this module.
data TypeInferenceState = TypeInferenceState
  { typeEquations :: [TypeEquation]
    -- ^ The type equations that have to be unified.
  , typeAssumption :: TypeAssumption
    -- ^ The known type schemas of predefined functions and constructors.
  , fixedTypeArgs :: Map HS.QName [HS.Type]
    -- ^ Maps function names to the types to instantiate their last type
    --   arguments with. This is used to instantiate additional type arguments
    --   in recursive functions correctly.
  }

-- | An empty 'TypeInferenceState'.
emptyTypeInferenceState :: TypeInferenceState
emptyTypeInferenceState = TypeInferenceState { typeEquations  = []
                                             , typeAssumption = Map.empty
                                             , fixedTypeArgs  = Map.empty
                                             }

-- | Creates a 'TypeAssumption' for all funtions and constructors defined
--   in the given environment.
makeTypeAssumption :: Environment -> TypeAssumption
makeTypeAssumption env = Map.fromList
  [ (name, typeSchema)
  | (scope, name) <- Map.keys (envEntries env)
  , scope == ValueScope
  , typeSchema <- maybeToList (lookupTypeSchema scope name env)
  ]

-- | The state monad used throughout this module.
newtype TypeInference a = TypeInference
  { unwrapTypeInference :: StateT TypeInferenceState Converter a }
 deriving
  (Functor, Applicative, Monad, MonadState TypeInferenceState, MonadFail)

-- | Messages can be reported during type inference.
instance MonadReporter TypeInference where
  liftReporter = liftConverter . liftReporter

-- | Lifts a converter into the type inference monad.
instance MonadConverter TypeInference where
  liftConverter = TypeInference . lift

-- | Runs the 'TypeInference' monad with the given initial type assumption.
runTypeInference :: TypeAssumption -> TypeInference a -> Converter a
runTypeInference initialTypeAssumption =
  flip evalStateT initialState . unwrapTypeInference
 where
  initialState :: TypeInferenceState
  initialState =
    emptyTypeInferenceState { typeAssumption = initialTypeAssumption }

-------------------------------------------------------------------------------
-- Type inference state inspection                                           --
-------------------------------------------------------------------------------

-- | Looks up the type schema of the function or constructor with the given
--   name in the current type assumption.
lookupTypeAssumption :: HS.QName -> TypeInference (Maybe HS.TypeSchema)
lookupTypeAssumption name = Map.lookup name <$> gets typeAssumption

-- | Looks up the types to instantiate the additional type arguments
--   of the function with the given name with.
lookupFixedTypeArgs :: HS.QName -> TypeInference [HS.Type]
lookupFixedTypeArgs name = Map.findWithDefault [] name <$> gets fixedTypeArgs

-------------------------------------------------------------------------------
-- Type inference state manipulation                                         --
-------------------------------------------------------------------------------

-- | Adds a 'TypeEquation' entry the current state.
addTypeEquation :: SrcSpan -> HS.Type -> HS.Type -> TypeInference ()
addTypeEquation srcSpan t t' =
  modify $ \s -> s { typeEquations = (srcSpan, t, t') : typeEquations s }

-- | Instantiates the type schema of the function or constructor with the
--   given name and adds a 'TypeEquation' for the resulting type and the
--   given type to the current state.
--
--   If there is no entry for the given name, a fatal error is reported.
--   The error message refers to the given source location information.
addTypeEquationFor :: SrcSpan -> HS.QName -> HS.Type -> TypeInference ()
addTypeEquationFor srcSpan name resType = do
  maybeTypeSchema <- lookupTypeAssumption name
  case maybeTypeSchema of
    Nothing ->
      reportFatal
        $  Message NoSrcSpan Error
        $  "Identifier not in scope "
        ++ showPretty name
    Just typeSchema -> do
      typeExpr <- liftConverter $ instantiateTypeSchema typeSchema
      addTypeEquation srcSpan typeExpr resType

-- | Extends the type assumption with the type schema for the function,
--   constructor or local variable with the given name.
extendTypeAssumption :: HS.QName -> HS.TypeSchema -> TypeInference ()
extendTypeAssumption name typeSchema = do
  modify $ \s ->
    s { typeAssumption = Map.insert name typeSchema (typeAssumption s) }

-- | Extends the type assumption with the type schema for the given function
--   declaration if all of its argument and return types are annotated.
extendTypeAssumptionWithFuncDecl :: HS.FuncDecl -> TypeInference ()
extendTypeAssumptionWithFuncDecl funcDecl =
  case HS.funcDeclTypeSchema funcDecl of
    Nothing -> return ()
    Just typeSchema ->
      extendTypeAssumption (HS.funcDeclQName funcDecl) typeSchema

-- | Extends the type assumption with the unabstracted type the given
--   variable pattern has been annotated with.
extendTypeAssumptionWithVarPat :: HS.VarPat -> TypeInference ()
extendTypeAssumptionWithVarPat varPat = case HS.varPatType varPat of
  Nothing         -> return ()
  Just varPatType -> extendTypeAssumption
    (HS.varPatQName varPat)
    (HS.TypeSchema NoSrcSpan [] varPatType)

-- | Removes the variable bound by the given variable pattern from the
--   type assumption while runnign the given type inference.
removeVarPatFromTypeAssumption :: HS.VarPat -> TypeInference ()
removeVarPatFromTypeAssumption varPat = do
  modify $ \s -> s
    { typeAssumption = Map.delete (HS.varPatQName varPat) (typeAssumption s)
    }

-- | Sets the types to instantiate additional type arguments of the function
--   with the given name with.
fixTypeArgs :: HS.QName -> [HS.Type] -> TypeInference ()
fixTypeArgs name subst =
  modify $ \s -> s { fixedTypeArgs = Map.insert name subst (fixedTypeArgs s) }

-------------------------------------------------------------------------------
-- Scoping                                                                   --
-------------------------------------------------------------------------------

-- | Runs the given type inference and discards all modifications o fthe
--   state afterwards.
withLocalState :: TypeInference a -> TypeInference a
withLocalState mx = do
  oldState <- get
  x        <- mx
  put oldState
  return x

-- | Runs the given type inference and discards all modifications of the
--   type assumption afterwards.
withLocalTypeAssumption :: TypeInference a -> TypeInference a
withLocalTypeAssumption mx = do
  oldTypeAssumption <- gets typeAssumption
  x                 <- mx
  modify $ \s -> s { typeAssumption = oldTypeAssumption }
  return x

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Infers the types of (mutually recursive) function declarations.
--
--   Returns the function declarations where the argument and return types
--   as well as the types of variable patterns on the right-hand side and
--   visible type arguments have been annotated with their inferred type.
inferFuncDeclTypes :: [HS.FuncDecl] -> Converter [HS.FuncDecl]
inferFuncDeclTypes funcDecls = localEnv $ do
  ta <- inEnv makeTypeAssumption
  runTypeInference ta $ inferFuncDeclTypes' funcDecls

-- | Version of 'inferFuncDeclTypes' in the 'TypeInference' monad.
inferFuncDeclTypes' :: [HS.FuncDecl] -> TypeInference [HS.FuncDecl]
inferFuncDeclTypes' funcDecls = withLocalState $ do
    -- Add type assumption for functions with type signatures.
    --
    -- This is required such that polymorphically recursive functions don't
    -- cause a type error.
  mapM_ extendTypeAssumptionWithFuncDecl funcDecls

  -- Add type annotations.
  --
  -- TODO
  annotatedFuncDecls <- annotateFuncDecls funcDecls

  -- Unify type equations.
  --
  -- During the annotation of the function declaration type equations were
  -- added. The system of type equations is solved by computing the most
  -- general unificator (mgu).
  eqns               <- gets typeEquations
  mgu                <- liftConverter $ unifyEquations eqns
  typedFuncDecls     <- liftConverter $ mapM (applySubst mgu) annotatedFuncDecls

  -- Abstract inferred type to type schema.
  --
  -- The function takes one type argument for each type variable in the
  -- inferred type expression. Additional type arguments that occur in
  -- type signatures and visible type applications on the right-hand side
  -- of the function but not in the inferred type (also known as "vanishing
  -- type  arguments") are added as well. The order of the type arguments
  -- depends on their order in the (type) expression (from left to right).
  let
    typeExprs = map (fromJust . HS.funcDeclType) typedFuncDecls
    typeArgs  = map typeVars typeExprs
    additionalTypeArgs =
      nub (concatMap typeVars typedFuncDecls) \\ concat typeArgs
    allTypeArgs = map (++ additionalTypeArgs) typeArgs
  abstractedFuncDecls <- liftConverter
    $ zipWithM abstractTypeArgs allTypeArgs typedFuncDecls

  -- Fix instantiation of additional type arguments.
  --
  -- The additional type arguments must be passed unchanged in recursive
  -- calls (otherwise there would have to be an infinite number of type
  -- arguments). However, 'applyFuncDeclVisibly' would instantiate them
  -- with fresh type variables since they do not occur in the inferred
  -- type the application has been annotated with. Thus, we have to
  -- remember for each function in the strongly connected component,
  -- the type to instantiate the remaining type arguments with. The
  -- fixed type arguments will be taken into account by 'applyVisibly'.
  let funcNames           = map HS.funcDeclQName abstractedFuncDecls
      additionalTypeArgs' = map
        ( map HS.typeVarDeclToType
        . takeEnd (length additionalTypeArgs)
        . HS.funcDeclTypeArgs
        )
        abstractedFuncDecls
  zipWithM_ fixTypeArgs funcNames additionalTypeArgs'

  -- Add visible type applications.
  --
  -- Now that we also know the type arguments of the functions in then
  -- strongly connected component, we can replace the type annotations
  -- for function and constructor applications added by 'annotateFuncDecl'
  -- by visible type applications.
  mapM_ extendTypeAssumptionWithFuncDecl abstractedFuncDecls
  visiblyAppliedFuncDecls <- mapM applyFuncDeclVisibly abstractedFuncDecls

  -- Abstract new vanishing type arguments.
  --
  -- The instatiation of type schemas by 'applyFuncDeclVisibly' might
  -- have introduced new vanishing type arguments if a function with
  -- vanishing type arguments is applied that does not occur in the
  -- strongly connected component. Those additional type arguments
  -- need to be abstracted as well.
  liftConverter $ abstractVanishingTypeArgs visiblyAppliedFuncDecls

-------------------------------------------------------------------------------
-- Type annotations                                                          --
-------------------------------------------------------------------------------

-- | Generates a fresh type variable if the given type is @Nothing@
--   and returns the given type otherwise.
maybeFreshTypeVar :: Maybe HS.Type -> TypeInference HS.Type
maybeFreshTypeVar = liftConverter . maybe freshTypeVar return

-- | Annotates the type of the given variable pattern using a fresh type
--   variable if there is no type annotation already and extends the type
--   assumption by the (unabstracted) type for the declared variable.
annotateVarPat :: HS.VarPat -> TypeInference HS.VarPat
annotateVarPat varPat = do
  varPatType' <- maybeFreshTypeVar (HS.varPatType varPat)
  let varPat' = varPat { HS.varPatType = Just varPatType' }
  extendTypeAssumptionWithVarPat varPat'
  return varPat'

-- | Annotates the given expression with the given type if it does not have
--   a type annotation already and annotates the expression recursively.
--
--   If the type (or the general structure of the type) of the given expression
--   is known, type equations are added. For example, if a function is
--   predefined, it is known that its type must be an instance of its type
--   schema. Thus, the type schema is instantiated with fresh type variables
--   and a type equation is added that unifies the expected type with the given
--   type.
--
--   If there are variable patterns, they are annotated with fresh type
--   variables and inserted (unabstracted) into the local type assumption.
--   Thus, all references to local variables are annotated with the same type
--   as the variable pattern they are bound by and there are type equations
--   that unify the annotated type with the given type.
--
--   If the type of the expression is annotated already (e.g., through an
--   expression type signature), a type equation is added that unifies the
--   annotated type with the given type. The annotated expression keeps its
--   original annotation.
annotateExprWith :: HS.Expr -> HS.Type -> TypeInference HS.Expr
annotateExprWith expr resType = case HS.exprTypeSchema expr of
  Nothing         -> annotateExprWith' expr resType
  Just typeSchema -> do
    exprType <- liftConverter $ instantiateTypeSchema typeSchema
    addTypeEquation (HS.exprSrcSpan expr) exprType resType
    annotateExprWith' expr exprType

-- | Version of 'annotateExprWith' that ignores existing type annotations.
annotateExprWith' :: HS.Expr -> HS.Type -> TypeInference HS.Expr

-- If @C :: τ@ is a predefined constructor with @C :: forall α₀ … αₙ. τ'@,
-- then add a type equation @τ = σ(τ')@ where @σ = { α₀ ↦ β₀, …, αₙ ↦ βₙ }@
-- and @β₀, …, βₙ@ are fresh type variables.
annotateExprWith' (HS.Con srcSpan conName _) resType = do
  addTypeEquationFor srcSpan conName resType
  return (HS.Con srcSpan conName (makeExprType resType))

-- If @x :: τ@ is in scope with @x :: forall α₀ … αₙ. τ'@, then add a type
-- equation @τ = σ(τ')@ where @σ = { α₀ ↦ β₀, …, αₙ ↦ βₙ }@ and @β₀, …, βₙ@
-- are fresh type variables.
-- In case of local variables or functions whose types are currently inferred,
-- the type assumption of @x@ is not abstracted (i.e., @n = 0@).
-- Therfore a type equation that unifies the type the binder of @x@ has been
-- annotated with and the given type @τ@ is simply added in this case.
annotateExprWith' (HS.Var srcSpan varName _) resType = do
  addTypeEquationFor srcSpan varName resType
  return (HS.Var srcSpan varName (makeExprType resType))

-- If @(e₁ e₂) :: τ@, then @e₁ :: α -> τ@ and @e₂ :: α@ where @α@ is a fresh
-- type variable.
annotateExprWith' (HS.App srcSpan e1 e2 _) resType = do
  argType <- liftConverter freshTypeVar
  e1'     <- annotateExprWith e1 (HS.FuncType NoSrcSpan argType resType)
  e2'     <- annotateExprWith e2 argType
  return (HS.App srcSpan e1' e2' (makeExprType resType))

-- There should be no visible type applications prior to type inference.
annotateExprWith' (HS.TypeAppExpr srcSpan _ _ _) _ =
  unexpectedTypeAppExpr srcSpan

-- If @if e₁ then e₂ else e₃ :: τ@, then @e₁ :: Bool@ and @e₂, e₃ :: τ@.
annotateExprWith' (HS.If srcSpan e1 e2 e3 _) resType = do
  let condType = HS.TypeCon NoSrcSpan HS.boolTypeConName
  e1' <- annotateExprWith e1 condType
  e2' <- annotateExprWith e2 resType
  e3' <- annotateExprWith e3 resType
  return (HS.If srcSpan e1' e2' e3' (makeExprType resType))

-- If @case e of {p₀ -> e₀; …; pₙ -> eₙ} :: τ@, then @e₀, …, eₙ :: τ@ and
-- @e :: α@ and @p₀, …, pₙ :: α@ where @α@ is a fresh type variable.
annotateExprWith' (HS.Case srcSpan scrutinee alts _) resType = do
  scrutineeType <- liftConverter freshTypeVar
  scrutinee'    <- annotateExprWith scrutinee scrutineeType
  alts'         <- mapM (flip annotateAlt scrutineeType) alts
  return (HS.Case srcSpan scrutinee' alts' (makeExprType resType))
 where
  -- | Annotates the pattern of the given alternative with the given type
  --   and its right-hand side with the @case@ expressions result type.
  annotateAlt :: HS.Alt -> HS.Type -> TypeInference HS.Alt
  annotateAlt (HS.Alt altSrcSpan conPat varPats rhs) patType =
    withLocalTypeAssumption $ do
      varPats' <- mapM annotateVarPat varPats
      let varPatTypes = map (fromJust . HS.varPatType) varPats'
          conPatType  = HS.funcType NoSrcSpan varPatTypes patType
      addTypeEquationFor altSrcSpan (HS.conPatName conPat) conPatType
      rhs' <- annotateExprWith rhs resType
      return (HS.Alt altSrcSpan conPat varPats' rhs')

-- Error terms are predefined polymorphic funtions. They can be annoated
-- with the given result type directly.
annotateExprWith' (HS.Undefined srcSpan _) resType =
  return (HS.Undefined srcSpan (makeExprType resType))
annotateExprWith' (HS.ErrorExpr srcSpan msg _) resType =
  return (HS.ErrorExpr srcSpan msg (makeExprType resType))

-- If @n :: τ@ for some integer literal @n@, then add the type equation
-- @τ = Integer@.
annotateExprWith' (HS.IntLiteral srcSpan value _) resType = do
  let intType = HS.TypeCon NoSrcSpan HS.integerTypeConName
  addTypeEquation srcSpan intType resType
  return (HS.IntLiteral srcSpan value (makeExprType resType))

-- If @\\x₀ … xₙ -> e :: τ@, then @x₀ :: α₀, …, xₙ :: αₙ@ and @x :: β@ for
-- fresh type variables @α₀, …, αₙ@ and @β@ and add the a type equation
-- @α₀ -> … -> αₙ -> β = τ@.
annotateExprWith' (HS.Lambda srcSpan args expr _) resType =
  withLocalTypeAssumption $ do
    args'   <- mapM annotateVarPat args
    retType <- liftConverter freshTypeVar
    expr'   <- annotateExprWith expr retType
    let argTypes = map (fromJust . HS.varPatType) args'
        funcType = HS.funcType NoSrcSpan argTypes retType
    addTypeEquation srcSpan funcType resType
    return (HS.Lambda srcSpan args' expr' (makeExprType resType))

-- | Utility function used by 'annotateExprWith' to construct the
--   'HS.exprTypeSchema' field.
--
--   Never returns @Nothing@ since all expressions must be annotated by
--   'annotateExprWith'. The type schema does not quantify any variables.
--   Type variables will be bound by the function declaration that contains
--   the expression.
makeExprType :: HS.Type -> Maybe HS.TypeSchema
makeExprType = Just . HS.TypeSchema NoSrcSpan []

-- | Annotates the function arguments and return types with fresh type
--   variables if they are not annotated already and applies 'annotateExprWith'
--   to the right-hand side of the given function declaration with the
--   return type of the function.
annotateFuncDecls :: [HS.FuncDecl] -> TypeInference [HS.FuncDecl]
annotateFuncDecls funcDecls = withLocalTypeAssumption $ do
  funcDecls' <- mapM annotateFuncDeclLhs funcDecls
  mapM_ extendTypeAssumptionWithFuncDecl funcDecls'
  mapM annotateFuncDeclRhs funcDecls'
 where
  -- | Annotates the argument and return types of the given function
  --   declaration.
  annotateFuncDeclLhs :: HS.FuncDecl -> TypeInference HS.FuncDecl
  annotateFuncDeclLhs funcDecl = withLocalTypeAssumption $ do
    args'   <- mapM annotateVarPat (HS.funcDeclArgs funcDecl)
    retType <- maybeFreshTypeVar (HS.funcDeclReturnType funcDecl)
    return funcDecl { HS.funcDeclArgs       = args'
                    , HS.funcDeclReturnType = Just retType
                    }

  -- | Annotates the right-hand side of the given function declaration.
  annotateFuncDeclRhs :: HS.FuncDecl -> TypeInference HS.FuncDecl
  annotateFuncDeclRhs funcDecl = withLocalTypeAssumption $ do
    let Just retType = HS.funcDeclReturnType funcDecl
    mapM_ extendTypeAssumptionWithVarPat (HS.funcDeclArgs funcDecl)
    rhs' <- annotateExprWith (HS.funcDeclRhs funcDecl) retType
    return funcDecl { HS.funcDeclRhs = rhs' }

-------------------------------------------------------------------------------
-- Visible type application                                                  --
-------------------------------------------------------------------------------

-- | Adds visible type application expressions to a function or constructor
--   with the given name.
--
--   Unifies the type annotations added by 'annotateExprWith' and the assumed
--   type schema for the function or constructor to infer the type arguments.
--   If the function or constructor has vanishing type arguments, this function
--   introduces new vanishing type variables to the expression that have to be
--   abstracted later (See 'abstractVanishingTypeArgs').
--
--   Since the expression has been annotated with 'annotateExprWith', we
--   can safely assume, that 'HS.exprTypeSchema' does not quantify any type
--   variables itself.
applyVisibly :: HS.QName -> HS.Expr -> TypeInference HS.Expr
applyVisibly name expr = do
  let srcSpan = HS.exprSrcSpan expr
      Just annotatedType = HS.exprType expr
  maybeAssumedTypeSchema <- lookupTypeAssumption name
  case maybeAssumedTypeSchema of
    Nothing                -> return expr
    Just assumedTypeSchema -> do
      (assumedType, typeArgs) <- liftConverter
        $ instantiateTypeSchema' assumedTypeSchema
      mgu       <- liftConverter $ unifyOrFail srcSpan annotatedType assumedType
      fixed     <- lookupFixedTypeArgs name
      typeArgs' <- liftConverter
        $ mapM (applySubst mgu) (dropEnd (length fixed) typeArgs)
      return (HS.visibleTypeApp srcSpan expr (typeArgs' ++ fixed))

-- | Adds visible type application expressions to function and constructor
--   applications in the given expression.
applyExprVisibly :: HS.Expr -> TypeInference HS.Expr

-- Add visible type applications to functions, constructors and error terms.
-- We can assume that the expression has a type annotation without quantified
-- type variables since 'annotateExprWith' was applied before.
applyExprVisibly expr@(HS.Con _ conName _) = applyVisibly conName expr
applyExprVisibly expr@(HS.Var _ varName _) = applyVisibly varName expr
applyExprVisibly expr@(HS.Undefined srcSpan exprType) = do
  let Just (HS.TypeSchema _ [] typeArg) = exprType
  return (HS.TypeAppExpr srcSpan expr typeArg exprType)
applyExprVisibly expr@(HS.ErrorExpr srcSpan _ exprType) = do
  let Just (HS.TypeSchema _ [] typeArg) = exprType
  return (HS.TypeAppExpr srcSpan expr typeArg exprType)

-- There should be no visible type applications prior to type inference.
applyExprVisibly (HS.TypeAppExpr srcSpan _ _ _) = unexpectedTypeAppExpr srcSpan

-- Recursively add visible type applications.
applyExprVisibly (HS.App srcSpan e1 e2 exprType) = do
  e1' <- applyExprVisibly e1
  e2' <- applyExprVisibly e2
  return (HS.App srcSpan e1' e2' exprType)
applyExprVisibly (HS.If srcSpan e1 e2 e3 exprType) = do
  e1' <- applyExprVisibly e1
  e2' <- applyExprVisibly e2
  e3' <- applyExprVisibly e3
  return (HS.If srcSpan e1' e2' e3' exprType)
applyExprVisibly (HS.Case srcSpan expr alts exprType) = do
  expr' <- applyExprVisibly expr
  alts' <- mapM applyAltVisibly alts
  return (HS.Case srcSpan expr' alts' exprType)
applyExprVisibly (HS.Lambda srcSpan args expr exprType) =
  withLocalTypeAssumption $ do
    mapM_ removeVarPatFromTypeAssumption args
    expr' <- applyExprVisibly expr
    return (HS.Lambda srcSpan args expr' exprType)

-- Leave all literals unchanged.
applyExprVisibly expr@(HS.IntLiteral _ _ _) = return expr

-- | Applies 'applyExprVisibly' to the right-hand side of the given @case@-
--   expression alternative.
applyAltVisibly :: HS.Alt -> TypeInference HS.Alt
applyAltVisibly (HS.Alt srcSpan conPat varPats expr) =
  withLocalTypeAssumption $ do
    mapM_ removeVarPatFromTypeAssumption varPats
    expr' <- applyExprVisibly expr
    return (HS.Alt srcSpan conPat varPats expr')

-- | Applies ' applyExprVisibly' to the right-hand side of the given function
--   declaration.
applyFuncDeclVisibly :: HS.FuncDecl -> TypeInference HS.FuncDecl
applyFuncDeclVisibly funcDecl = withLocalTypeAssumption $ do
  let args = HS.funcDeclArgs funcDecl
      rhs  = HS.funcDeclRhs funcDecl
  mapM_ removeVarPatFromTypeAssumption args
  rhs' <- applyExprVisibly rhs
  return funcDecl { HS.funcDeclRhs = rhs' }

-------------------------------------------------------------------------------
-- Abstracting type arguments                                                --
-------------------------------------------------------------------------------

-- | Normalizes the names of the given type variables and adds them as type
--   arguments to the function declaration.
--
--   The first argument contains the names of type variables that should be
--   bound by type arguments. Usually these are the type variables that
--   occur in the function declaration's type and on its right-hand side.
--
--   Fresh type variables used by the given type are replaced by regular type
--   varibales with the prefix 'freshTypeArgPrefix'. All other type variables
--   are not renamed.
abstractTypeArgs :: [HS.QName] -> HS.FuncDecl -> Converter HS.FuncDecl
abstractTypeArgs typeArgs funcDecl = do
  let HS.TypeSchema _ _ typeExpr = fromJust (HS.funcDeclTypeSchema funcDecl)
  (HS.TypeSchema _ typeArgs' _, subst) <- abstractTypeSchema' typeArgs typeExpr
  funcDecl'                            <- applySubst subst funcDecl
  return funcDecl' { HS.funcDeclTypeArgs = typeArgs' }

-- | Abstracts the remaining internal type variables that occur within
--   the given function declarations by renaming them to non-internal
--   type variables and adding them as type arguments to the function
--   declarations.
--
--   The added type arguments are also added as visible type applications
--   to recursive calls to the function declarations.
abstractVanishingTypeArgs :: [HS.FuncDecl] -> Converter [HS.FuncDecl]
abstractVanishingTypeArgs funcDecls = do
  funcDecls' <- mapM addInternalTypeArgs funcDecls
  mapM abstractVanishingTypeArgs' funcDecls'
 where
  -- | The names of the type variables to abstract.
  internalTypeArgNames :: [HS.QName]
  internalTypeArgNames = filter HS.isInternalQName (typeVars funcDecls)

  -- | Type variables for 'internalTypeArgNames'.
  internalTypeArgs :: [HS.Type]
  internalTypeArgs = map
    (HS.TypeVar NoSrcSpan . fromJust . HS.identFromQName)
    internalTypeArgNames

  -- | Renames 'internalTypeArgNames' and adds them as type arguments
  --   to the given function declaration.
  abstractVanishingTypeArgs' :: HS.FuncDecl -> Converter HS.FuncDecl
  abstractVanishingTypeArgs' funcDecl = do
    let typeArgNames = map HS.typeVarDeclQName (HS.funcDeclTypeArgs funcDecl)
    abstractTypeArgs (typeArgNames ++ internalTypeArgNames) funcDecl

  -- | Adds visible type applications for 'internalTypeArgs' to recursive
  --   calls on the right-hand side of the given function declaration.
  --
  --   TODO move out of @Converter@ monad.
  addInternalTypeArgs :: HS.FuncDecl -> Converter HS.FuncDecl
  addInternalTypeArgs funcDecl = do
    let funcNames  = Set.fromList (map HS.funcDeclQName funcDecls)
        funcNames' = withoutArgs (HS.funcDeclArgs funcDecl) funcNames
        rhs        = HS.funcDeclRhs funcDecl
        rhs'       = addInternalTypeArgsToExpr funcNames' rhs
    return funcDecl { HS.funcDeclRhs = rhs' }

  -- | Adds visible type applications for 'internalTypeArgs' to recursive
  --   calls in the given expression.
  addInternalTypeArgsToExpr :: Set HS.QName -> HS.Expr -> HS.Expr
  addInternalTypeArgsToExpr =
    uncurry (HS.visibleTypeApp NoSrcSpan) .: addInternalTypeArgsToExpr'

  -- | Like 'addInternalTypeArgs' but returns the visible type
  --   arguments that still need to be added.
  addInternalTypeArgsToExpr' :: Set HS.QName -> HS.Expr -> (HS.Expr, [HS.Type])

  -- If this is a recursive call the internal type arguments need to be
  -- applied visibly.
  addInternalTypeArgsToExpr' funcNames expr@(HS.Var _ varName _)
    | varName `Set.member` funcNames = (expr, internalTypeArgs)
    | otherwise                      = (expr, [])

  -- Add new type arguments after exisiting visible type applications.
  addInternalTypeArgsToExpr' funcNames (HS.TypeAppExpr srcSpan expr typeExpr exprType)
    = let (expr', typeArgs) = addInternalTypeArgsToExpr' funcNames expr
      in  (HS.TypeAppExpr srcSpan expr' typeExpr exprType, typeArgs)

  -- Recursively add the internal type arguments.
  addInternalTypeArgsToExpr' funcNames (HS.App srcSpan e1 e2 exprType) =
    let e1' = addInternalTypeArgsToExpr funcNames e1
        e2' = addInternalTypeArgsToExpr funcNames e2
    in  (HS.App srcSpan e1' e2' exprType, [])
  addInternalTypeArgsToExpr' funcNames (HS.If srcSpan e1 e2 e3 exprType) =
    let e1' = addInternalTypeArgsToExpr funcNames e1
        e2' = addInternalTypeArgsToExpr funcNames e2
        e3' = addInternalTypeArgsToExpr funcNames e3
    in  (HS.If srcSpan e1' e2' e3' exprType, [])
  addInternalTypeArgsToExpr' funcNames (HS.Case srcSpan expr alts exprType) =
    let expr' = addInternalTypeArgsToExpr funcNames expr
        alts' = map (addInternalTypeArgsToAlt funcNames) alts
    in  (HS.Case srcSpan expr' alts' exprType, [])
  addInternalTypeArgsToExpr' funcNames (HS.Lambda srcSpan args expr exprType) =
    let funcNames' = withoutArgs args funcNames
        expr'      = addInternalTypeArgsToExpr funcNames' expr
    in  (HS.Lambda srcSpan args expr' exprType, [])

  -- Leave all other expressions unchnaged.
  addInternalTypeArgsToExpr' _ expr@(HS.Con        _ _ _) = (expr, [])
  addInternalTypeArgsToExpr' _ expr@(HS.IntLiteral _ _ _) = (expr, [])
  addInternalTypeArgsToExpr' _ expr@(HS.Undefined _ _   ) = (expr, [])
  addInternalTypeArgsToExpr' _ expr@(HS.ErrorExpr _ _ _ ) = (expr, [])

  -- | Applies 'addInternalTypeArgsToExpr' to the right-hand side of
  --   the given @case@ expression alternative.
  addInternalTypeArgsToAlt :: Set HS.QName -> HS.Alt -> HS.Alt
  addInternalTypeArgsToAlt funcNames (HS.Alt srcSpan conPat varPats expr) =
    let funcNames' = withoutArgs varPats funcNames
        expr'      = addInternalTypeArgsToExpr funcNames' expr
    in  HS.Alt srcSpan conPat varPats expr'

  -- | Removes the names of the given variable patterns from the given set.
  withoutArgs :: [HS.VarPat] -> Set HS.QName -> Set HS.QName
  withoutArgs = flip (Set.\\) . Set.fromList . map HS.varPatQName

-------------------------------------------------------------------------------
-- Solving type equations                                                    --
-------------------------------------------------------------------------------

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
-- Error reporting                                                           --
-------------------------------------------------------------------------------

-- | Reports an internal error when a type application expression is
--   encountered prior to type inference.
unexpectedTypeAppExpr :: MonadReporter r => SrcSpan -> r a
unexpectedTypeAppExpr srcSpan =
  reportFatal
    $ Message srcSpan Internal
    $ "Unexpected visible type application."
