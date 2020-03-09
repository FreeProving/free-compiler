{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
                                                , zipWithM
                                                , zipWithM_
                                                )
import           Control.Monad.State            ( MonadState
                                                , StateT(..)
                                                , evalStateT
                                                , gets
                                                , modify
                                                )
import           Data.List                      ( (\\)
                                                , nub
                                                , partition
                                                )
import           Data.List.Extra                ( dropEnd )
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

-------------------------------------------------------------------------------
-- Type inference state monad                                                --
-------------------------------------------------------------------------------

-- | A pair of a variable name and its expected type type and location in the
--   source code.
type TypedVar = (HS.VarName, (SrcSpan, HS.Type))

-- | A type equation and the location in the source that caused the creation
--   of this type variable.
type TypeEquation = (SrcSpan, HS.Type, HS.Type)

-- | Maps the names of defined functions and constructors to their type schema.
type TypeAssumption = Map HS.QName HS.TypeSchema

-- | The state that is passed implicitly between the modules of this module.
data TypeInferenceState = TypeInferenceState
  { varTypes :: [TypedVar]
    -- ^ The constraints for types of variables added during the simplification
    --   of expression/type pairs.
  , typeEquations :: [TypeEquation]
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
emptyTypeInferenceState = TypeInferenceState
  { varTypes       = []
  , typeEquations  = []
  , typeAssumption = Map.empty
  , fixedTypeArgs  = Map.empty
  }

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

-- | The state monad used throughout this module.
newtype TypeInference a = TypeInference
  { unwrapTypeInference :: StateT TypeInferenceState Converter a }
 deriving
  (Functor, Applicative, Monad, MonadState TypeInferenceState)

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

-- | Gets the 'TypeEquation' entries from the current state and
--   constructors 'TypeEquation' entries from the 'TypedVar' entries
--   using 'makeTypeEquations'.
getAllTypeEquations :: TypeInference [TypeEquation]
getAllTypeEquations =
  (++) <$> (makeTypeEquations <$> gets varTypes) <*> gets typeEquations

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

-- | Adds a 'TypedVar' entry to the current state.
addVarType :: SrcSpan -> HS.QName -> HS.Type -> TypeInference ()
addVarType srcSpan v t =
  modify $ \s -> s { varTypes = (v, (srcSpan, t)) : varTypes s }

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
addTypeEquationOrVarTypeFor
  :: SrcSpan -> HS.QName -> HS.Type -> TypeInference ()
addTypeEquationOrVarTypeFor srcSpan name resType = do
  maybeTypeSchema <- lookupTypeAssumption name
  case maybeTypeSchema of
    Nothing         -> addVarType srcSpan name resType
    Just typeSchema -> do
      funcType <- liftConverter $ instantiateTypeSchema typeSchema
      addTypeEquation srcSpan funcType resType

-- | Extends the type assumption with the type schema for the function or
--   constructor with the given name.
--
--   Adds an entry for both the unqualified and the qualified name.
extendTypeAssumption :: HS.Name -> HS.TypeSchema -> TypeInference ()
extendTypeAssumption name typeSchema = do
  modName <- inEnv envModName
  extendTypeAssumption' (HS.UnQual name)       typeSchema
  extendTypeAssumption' (HS.Qual modName name) typeSchema

-- | Like 'extendTypeAssumption' but does not qualify the name automatically.
extendTypeAssumption' :: HS.QName -> HS.TypeSchema -> TypeInference ()
extendTypeAssumption' name typeSchema = do
  modify $ \s ->
    s { typeAssumption = Map.insert name typeSchema (typeAssumption s) }

-- | Remoes all variables bound by the given variable patterns from the
--   type assumption while running the given type inference.
removeVarPatsFromTypeAssumption
  :: [HS.VarPat] -> TypeInference a -> TypeInference a
removeVarPatsFromTypeAssumption = flip (foldr removeVarPatFromTypeAssumption)

-- | Removes the variable bound by the given variable pattern from the
--   type assumption while runnign the given type inference.
removeVarPatFromTypeAssumption
  :: HS.VarPat -> TypeInference a -> TypeInference a
removeVarPatFromTypeAssumption (HS.VarPat _ ident _) mx = do
  ta <- gets typeAssumption
  let name = HS.UnQual (HS.Ident ident)
      ta'  = Map.delete name ta
  modify $ \s -> s { typeAssumption = ta' }
  x <- mx
  modify $ \s -> s { typeAssumption = ta }
  return x

-- | Sets the types to instantiate additional type arguments of the function
--   with the given name with.
--
--   Adds an entry for both the unqualified and the qualified name.
fixTypeArgs :: HS.Name -> [HS.Type] -> TypeInference ()
fixTypeArgs name subst = do
  modName <- inEnv envModName
  fixTypeArgs' (HS.UnQual name)       subst
  fixTypeArgs' (HS.Qual modName name) subst

-- | Like 'fixTypeArgs' but does not qualify the name automatically.
fixTypeArgs' :: HS.QName -> [HS.Type] -> TypeInference ()
fixTypeArgs' name subst =
  modify $ \s -> s { fixedTypeArgs = Map.insert name subst (fixedTypeArgs s) }

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Tries to infer the types of (mutually recursive) function declarations.
inferFuncDeclTypes :: [HS.FuncDecl] -> Converter [HS.TypeSchema]
inferFuncDeclTypes = fmap snd . annotateFuncDeclTypes'

-- | Like 'inferFuncDeclTypes' but does not abstract the type to a type
--   schema and returns the substitution.
inferFuncDeclTypes' :: [HS.FuncDecl] -> TypeInference ([HS.Type], Subst HS.Type)
inferFuncDeclTypes' funcDecls = do
  (typedExprs, funcTypes) <- liftConverter
    $ mapAndUnzipM makeTypedExprs funcDecls
  zipWithM_ addTypeSigEquation funcDecls funcTypes
  mapM_ (uncurry simplifyTypedExpr) (concat typedExprs)
  eqns       <- getAllTypeEquations
  mgu        <- liftConverter $ unifyEquations eqns
  funcTypes' <- liftConverter $ mapM (applySubst mgu) funcTypes
  return (funcTypes', mgu)

-- | Creates fresh type variables @a@ and @a1 ... an@ and the expression/type
--   pairs @f :: a1 -> ... -> an -> a, x1 :: a1, ..., xn :: an@ and @e :: a@
--   for the given function declaration @f x1 ... xn = e@ and returns the
--   expression/type pairs as well as the type of the function.
makeTypedExprs :: HS.FuncDecl -> Converter ([(HS.Expr, HS.Type)], HS.Type)
makeTypedExprs (HS.FuncDecl _ (HS.DeclIdent srcSpan ident) _ args rhs maybeRetType)
  = do
    -- TODO instantiate argument and return types with fresh type arguments.
    (args', rhs') <- renameArgs args rhs
    argTypes      <- mapM makeArgType args
    retType       <- makeRetType
    let
      funcName = HS.UnQual (HS.Ident ident)
      funcExpr = HS.Var srcSpan funcName
      funcType = HS.funcType NoSrcSpan argTypes retType
      argExprs = map HS.varPatToExpr args'
      typedExprs =
        (funcExpr, funcType) : (rhs', retType) : zip argExprs argTypes
    return (typedExprs, funcType)
 where
  -- | Generates a fresh type variable for the given variable pattern or
  --   returns the annotated type variable.
  makeArgType :: HS.VarPat -> Converter HS.Type
  makeArgType (HS.VarPat _ _ Nothing       ) = freshTypeVar
  makeArgType (HS.VarPat _ _ (Just varType)) = return varType

  -- | Generates a fresh type variable for the function declaration's return
  --   type or returns the annotated type variable.
  makeRetType :: Converter HS.Type
  makeRetType = case maybeRetType of
    Nothing      -> freshTypeVar
    Just retType -> return retType

-- If the given function has a type signature @f :: τ@ and 'makeTypedExprs'
-- added the expression type pair @f :: τ'@, the type equation @τ = τ'@ is
-- added without instantiating the type variables in the type signature with
-- fresh identifiers such that the inferred type uses the same type variable
-- names as specified by the user.
addTypeSigEquation :: HS.FuncDecl -> HS.Type -> TypeInference ()
addTypeSigEquation funcDecl funcType = do
  let funcIdent = HS.fromDeclIdent (HS.getDeclIdent funcDecl)
      funcName  = HS.UnQual (HS.Ident funcIdent)
  maybeTypeSchema <- lookupTypeAssumption funcName
  case maybeTypeSchema of
    Nothing -> return ()
    Just (HS.TypeSchema srcSpan _ typeSig) ->
      -- TODO if we do not instantiate the type schema this may cause name
      --      conflicts.
      addTypeEquation srcSpan typeSig funcType

-- | Infers the types of type arguments to functions and constructors
--   used by the right-hand side of the given function declaration.
annotateFuncDeclTypes :: [HS.FuncDecl] -> Converter [HS.FuncDecl]
annotateFuncDeclTypes = fmap fst . annotateFuncDeclTypes'

-- | Like 'annotateFuncDeclTypes' but also returns the type of the
--   function declaration.
annotateFuncDeclTypes'
  :: [HS.FuncDecl] -> Converter ([HS.FuncDecl], [HS.TypeSchema])
annotateFuncDeclTypes' funcDecls = localEnv $ do
  ta <- inEnv makeTypeAssumtion
  runTypeInference ta $ do
      -- Add type annotations.
    annotatedFuncDecls <- liftConverter $ mapM annotateFuncDecl funcDecls
    -- Infer function types.
    (typeExprs, mgu) <- inferFuncDeclTypes' annotatedFuncDecls
    typedFuncDecls <- liftConverter $ mapM (applySubst mgu) annotatedFuncDecls
    -- Abstract inferred type schema.
    let typeArgs = map typeVars typeExprs
        additionalTypeArgs =
          nub (concatMap typeVars typedFuncDecls) \\ concat typeArgs
        allTypeArgs = map (++ additionalTypeArgs) typeArgs
    (typeSchemas, substs) <-
      liftConverter
      $   unzip
      <$> zipWithM abstractTypeSchema' allTypeArgs typeExprs
    abstractedFuncDecls <- liftConverter
      $ zipWithM applySubst substs typedFuncDecls
    -- The additional type arguments must not change.
    additionalTypeArgs' <- liftConverter $ mapM
      (\subst -> mapM
        (applySubst subst . HS.TypeVar NoSrcSpan . fromJust . HS.identFromQName)
        additionalTypeArgs
      )
      substs
    let funcNames =
          map (HS.Ident . HS.fromDeclIdent . HS.getDeclIdent) funcDecls
    zipWithM_ fixTypeArgs          funcNames additionalTypeArgs'
    -- Add visible type applications.
    zipWithM_ extendTypeAssumption funcNames typeSchemas
    visiblyAppliedFuncDecls <- mapM addTypeAppExprsToFuncDecl
                                    abstractedFuncDecls
    -- Abstract vanishing type arguments.
    liftConverter
      $   unzip
      <$> zipWithM abstractVanishingTypeArgs visiblyAppliedFuncDecls typeSchemas

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Tries to infer the type of the given expression from the current context
--   and abstracts it's type to a type schema.
inferExprType :: HS.Expr -> Converter HS.TypeSchema
inferExprType = fmap snd . annotateExprTypes'

-- | Like 'inferExprType' but does not abstract the type to a type schema and
--   also returns the substitution.
inferExprType' :: HS.Expr -> TypeInference (HS.Type, Subst HS.Type)
inferExprType' expr = do
  typeVar <- liftConverter freshTypeVar
  simplifyTypedExpr expr typeVar
  eqns     <- getAllTypeEquations
  mgu      <- liftConverter $ unifyEquations eqns
  exprType <- liftConverter $ applySubst mgu typeVar
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
  ta <- inEnv makeTypeAssumtion
  runTypeInference ta $ do
      -- Add type annotations.
    annotatedExpr   <- liftConverter $ annotateExpr expr
    -- Infer type.
    (typeExpr, mgu) <- inferExprType' annotatedExpr
    typedExpr       <- liftConverter $ applySubst mgu annotatedExpr
    -- Abstract inferred type schema.
    let typeArgs = nub (typeVars typedExpr ++ typeVars typeExpr)
    (typeSchema, subst) <- liftConverter $ abstractTypeSchema' typeArgs typeExpr
    abstractedExpr      <- liftConverter $ applySubst subst typedExpr
    -- Add visible type applications.
    expr'               <- addTypeAppExprs abstractedExpr
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
--   declaration and annotates the function arguments and return type
--   with fresh type variables.
--
--   Existing annotations of the argument and return types are discarded.
annotateFuncDecl :: HS.FuncDecl -> Converter HS.FuncDecl
annotateFuncDecl (HS.FuncDecl srcSpan declIdent _ args rhs _) = do
  args'   <- mapM annotateVarPat args
  rhs'    <- annotateExpr rhs
  retType <- freshTypeVar
  return (HS.FuncDecl srcSpan declIdent [] args' rhs' (Just retType))

-------------------------------------------------------------------------------
-- Visible type application                                                  --
-------------------------------------------------------------------------------

-- | Replaces a type signature added by 'annotateExpr' for a variable or
--   constructor with the given name by a visible type application of that
--   function or constructor.
addTypeAppExprsFor :: HS.QName -> HS.Expr -> HS.Type -> TypeInference HS.Expr
addTypeAppExprsFor name expr typeExpr = do
  maybeTypeSchema <- lookupTypeAssumption name
  case maybeTypeSchema of
    Nothing         -> return expr
    Just typeSchema -> do
      let srcSpan = HS.getSrcSpan expr
      (typeExpr', typeArgs) <- liftConverter $ instantiateTypeSchema' typeSchema
      mgu <- liftConverter $ unifyOrFail srcSpan typeExpr typeExpr'
      fixed                 <- lookupFixedTypeArgs name
      typeArgs'             <- liftConverter
        $ mapM (applySubst mgu) (dropEnd (length fixed) typeArgs)
      return (HS.visibleTypeApp srcSpan expr (typeArgs' ++ fixed))

-- | Replaces the type signatures added by 'annotateExpr' by visible type
--   application expressions.
addTypeAppExprs :: HS.Expr -> TypeInference HS.Expr

-- Add visible type applications to functions and constructors.
addTypeAppExprs (HS.ExprTypeSig _ expr@(HS.Con _ conName) (HS.TypeSchema _ [] typeExpr))
  = addTypeAppExprsFor conName expr typeExpr
addTypeAppExprs (HS.ExprTypeSig _ expr@(HS.Var _ varName) (HS.TypeSchema _ [] typeExpr))
  = addTypeAppExprsFor varName expr typeExpr

-- Add visible type applications to error terms.
addTypeAppExprs (HS.ExprTypeSig srcSpan expr@(HS.Undefined _) (HS.TypeSchema _ [] typeExpr))
  = return (HS.TypeAppExpr srcSpan expr typeExpr)
addTypeAppExprs (HS.ExprTypeSig srcSpan expr@(HS.ErrorExpr _ _) (HS.TypeSchema _ [] typeExpr))
  = return (HS.TypeAppExpr srcSpan expr typeExpr)

-- There should be no visible type applications prior to type inference.
addTypeAppExprs (HS.TypeAppExpr srcSpan _ _) = unexpectedTypeAppExpr srcSpan

-- Recursively add visible type applications.
addTypeAppExprs (HS.ExprTypeSig srcSpan expr typeSchema) = do
  expr' <- addTypeAppExprs expr
  return (HS.ExprTypeSig srcSpan expr' typeSchema)
addTypeAppExprs (HS.App srcSpan e1 e2) = do
  e1' <- addTypeAppExprs e1
  e2' <- addTypeAppExprs e2
  return (HS.App srcSpan e1' e2')
addTypeAppExprs (HS.If srcSpan e1 e2 e3) = do
  e1' <- addTypeAppExprs e1
  e2' <- addTypeAppExprs e2
  e3' <- addTypeAppExprs e3
  return (HS.If srcSpan e1' e2' e3')
addTypeAppExprs (HS.Case srcSpan expr alts) = do
  expr' <- addTypeAppExprs expr
  alts' <- mapM addTypeAppExprsToAlt alts
  return (HS.Case srcSpan expr' alts')
addTypeAppExprs (HS.Lambda srcSpan args expr) =
  removeVarPatsFromTypeAssumption args $ do
    expr' <- addTypeAppExprs expr
    return (HS.Lambda srcSpan args expr')

-- Leave all other expressions unchanged.
addTypeAppExprs expr@(HS.Con _ _       ) = return expr
addTypeAppExprs expr@(HS.Var _ _       ) = return expr
addTypeAppExprs expr@(HS.Undefined _   ) = return expr
addTypeAppExprs expr@(HS.ErrorExpr  _ _) = return expr
addTypeAppExprs expr@(HS.IntLiteral _ _) = return expr

-- | Applies 'addTypeAppExprs' to the right-hand side of the given @case@-
--   expression alternative.
addTypeAppExprsToAlt :: HS.Alt -> TypeInference HS.Alt
addTypeAppExprsToAlt (HS.Alt srcSpan conPat varPats expr) =
  removeVarPatsFromTypeAssumption varPats $ do
    expr' <- addTypeAppExprs expr
    return (HS.Alt srcSpan conPat varPats expr')

-- | Applies ' addTypeAppExprs' to the right-hand side of the given function
--   declaration.
addTypeAppExprsToFuncDecl :: HS.FuncDecl -> TypeInference HS.FuncDecl
addTypeAppExprsToFuncDecl funcDecl = do
  let args = HS.funcDeclArgs funcDecl
      rhs  = HS.funcDeclRhs funcDecl
  removeVarPatsFromTypeAssumption args $ do
    rhs' <- addTypeAppExprs rhs
    return funcDecl { HS.funcDeclRhs = rhs' }

-------------------------------------------------------------------------------
-- Abstracting type arguments                                                --
-------------------------------------------------------------------------------

-- | Abstracts the remaining internal type variables that occur within
--   the given function declaration by renaming them to non-internal
--   type variables and adding them to the @forall@ quantifier of the
--   given type schema.
abstractVanishingTypeArgs
  :: HS.FuncDecl -> HS.TypeSchema -> Converter (HS.FuncDecl, HS.TypeSchema)
abstractVanishingTypeArgs funcDecl (HS.TypeSchema _ typeArgs typeExpr) = do
  let typeArgNames = map (HS.UnQual . HS.Ident . HS.fromDeclIdent) typeArgs
      internalTypeArgNames = filter HS.isInternalQName (typeVars funcDecl)
  (typeSchema', subst) <- abstractTypeSchema'
    (typeArgNames ++ internalTypeArgNames)
    typeExpr
  funcDecl' <- applySubst subst funcDecl
  return (funcDecl', typeSchema')

-------------------------------------------------------------------------------
-- Simplification of expression/type pairs                                   --
-------------------------------------------------------------------------------

-- | Simplifies expression/type pairs to variables/type pairs and type
--   equations.
simplifyTypedExpr :: HS.Expr -> HS.Type -> TypeInference ()

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
  -> TypeInference ()
simplifyTypedAlt (HS.Alt _ conPat varPats expr) patType exprType = do
  (varPats', expr') <- liftConverter $ renameArgs varPats expr
  simplifyTypedPat conPat varPats' patType
  simplifyTypedExpr expr' exprType

-- | Applies 'simplifyTypedConPat' to the given constructor pattern and
--   'simplifyTypedVarPat' to the given variable patterns.
simplifyTypedPat :: HS.ConPat -> [HS.VarPat] -> HS.Type -> TypeInference ()
simplifyTypedPat conPat varPats patType = do
  varPatTypes <- liftConverter $ replicateM (length varPats) freshTypeVar
  let conPatType = HS.funcType NoSrcSpan varPatTypes patType
  simplifyTypedConPat conPat conPatType
  zipWithM_ simplifyTypedVarPat varPats varPatTypes

-- | Adds a type equation for the given constructor pattern that unifies the
--   given type with an instance of the constructor's type schema.
simplifyTypedConPat :: HS.ConPat -> HS.Type -> TypeInference ()
simplifyTypedConPat (HS.ConPat srcSpan conName) conPatType =
  addTypeEquationOrVarTypeFor srcSpan conName conPatType

-- | Adds two 'TypedVar' entries for the given variable pattern. One for
--   the given and one for the annotated type.
simplifyTypedVarPat :: HS.VarPat -> HS.Type -> TypeInference ()
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

-- | Like 'instantiateTypeSchema' but also returns the fresh type variables,
--   the type schema has been instantiated with.
instantiateTypeSchema' :: HS.TypeSchema -> Converter (HS.Type, [HS.Type])
instantiateTypeSchema' (HS.TypeSchema _ typeArgs typeExpr) = do
  (typeArgs', subst) <- renameTypeArgsSubst typeArgs
  typeExpr'          <- applySubst subst typeExpr
  let typeVars' = map (HS.TypeVar NoSrcSpan . HS.fromDeclIdent) typeArgs'
  return (typeExpr', typeVars')

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
--
--   Returns the resulting type schema and the substitution that replaces the
--   abstracted type variables by their name in the type schema.
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
