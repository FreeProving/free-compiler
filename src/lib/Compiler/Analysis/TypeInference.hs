{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | This module contains functions for infering the type of expressions
--   and function declarations as well as functions for annotating the types
--   of variable patterns and adding visible applications for type arguments.

module Compiler.Analysis.TypeInference
  ( addTypeSigsToFuncDecls
  , inferFuncDeclComponentTypes
  , inferFuncDeclTypes
  , inferExprType
  )
where

import           Control.Monad.Fail             ( MonadFail )
import           Control.Monad.Extra            ( mapAndUnzipM
                                                , replicateM
                                                , zipWithM
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
                                                , intercalate
                                                , nub
                                                , partition
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
import           Compiler.Environment
import           Compiler.Environment.Fresh
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Haskell.Subst
import           Compiler.Haskell.Unification
import           Compiler.Haskell.Inliner
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

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

-- | Extends the type assumption with the type schema for the given function
--   declaration if all of its argument and return types are annotated.
extendTypeAssumptionFor :: HS.FuncDecl -> TypeInference ()
extendTypeAssumptionFor funcDecl = do
  let funcName = HS.funcDeclName funcDecl
  case HS.funcDeclTypeSchema funcDecl of
    Nothing         -> return ()
    Just typeSchema -> extendTypeAssumption funcName typeSchema

-- | Removes the variable bound by the given variable pattern from the
--   type assumption while runnign the given type inference.
removeVarPatFromTypeAssumption :: HS.VarPat -> TypeInference ()
removeVarPatFromTypeAssumption varPat = do
  modify $ \s -> s
    { typeAssumption = Map.delete (HS.varPatQName varPat) (typeAssumption s)
    }

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
-- Scoping                                                                   --
-------------------------------------------------------------------------------

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
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | Annotates the given function declarations with the type from the
--   corresponding type signature.
--
--   Repots a fatal error if the type of an argument cannot be inferred from
--   the type signature (see 'splitFuncType').
--
--   Reports a fatal error if there are multiple type signatures for the same
--   function or a type signature lacks a corresponding function declaration.
addTypeSigsToFuncDecls
  :: [HS.TypeSig] -> [HS.FuncDecl] -> Converter [HS.FuncDecl]
addTypeSigsToFuncDecls typeSigs funcDecls = do
  mapM_ checkHasBinding typeSigs
  mapM addTypeSigToFuncDecl funcDecls
 where
  -- | Maps the names of functions to their annotated type.
  typeSigMap :: Map String [HS.TypeSchema]
  typeSigMap = Map.fromListWith
    (++)
    [ (ident, [typeSchema])
    | HS.TypeSig _ declIdents typeSchema <- typeSigs
    , HS.DeclIdent _ ident               <- declIdents
    ]

  -- | The names of all declared functions.
  funcDeclIdents :: Set String
  funcDeclIdents =
    Set.fromList $ map (HS.fromDeclIdent . HS.funcDeclIdent) funcDecls

  -- | Checks whether there is a function declaration for all functions
  --   annotated by the given type signature.
  checkHasBinding :: HS.TypeSig -> Converter ()
  checkHasBinding (HS.TypeSig _ declIdents _) =
    mapM_ checkHasBinding' declIdents

  -- | Checks whether there is a function declaration for the function
  --   with the given name.
  checkHasBinding' :: HS.DeclIdent -> Converter ()
  checkHasBinding' (HS.DeclIdent srcSpan ident)
    | ident `Set.member` funcDeclIdents
    = return ()
    | otherwise
    = report
      $  Message srcSpan Warning
      $  "The type signature for '"
      ++ ident
      ++ "' lacks an accompanying binding."

  addTypeSigToFuncDecl :: HS.FuncDecl -> Converter HS.FuncDecl
  addTypeSigToFuncDecl funcDecl = do
    let ident = HS.fromDeclIdent (HS.funcDeclIdent funcDecl)
        name  = HS.funcDeclQName funcDecl
        args  = HS.funcDeclArgs funcDecl
    case Map.lookup ident typeSigMap of
      Nothing -> return funcDecl
      Just [HS.TypeSchema _ typeArgs typeExpr] -> do
        (argTypes, retType) <- splitFuncType name args typeExpr
        let args' = zipWith
              (\arg argType -> arg { HS.varPatType = Just argType })
              args
              argTypes
        return funcDecl { HS.funcDeclTypeArgs   = typeArgs
                        , HS.funcDeclArgs       = args'
                        , HS.funcDeclReturnType = Just retType
                        }
      Just typeSchemas ->
        reportFatal
          $  Message (HS.funcDeclSrcSpan funcDecl) Error
          $  "Duplicate type signatures for '"
          ++ ident
          ++ "' at "
          ++ intercalate ", "
                         (map (showPretty . HS.typeSchemaSrcSpan) typeSchemas)

-- | Splits the annotated type of a Haskell function with the given arguments
--   into its argument and return types.
--
--   Type synonyms are expanded if neccessary.
splitFuncType
  :: HS.QName    -- ^ The name of the function to display in error messages.
  -> [HS.VarPat] -- ^ The argument variable patterns whose types to split of.
  -> HS.Type     -- ^ The type to split.
  -> Converter ([HS.Type], HS.Type)
splitFuncType name = splitFuncType'
 where
  splitFuncType' :: [HS.VarPat] -> HS.Type -> Converter ([HS.Type], HS.Type)
  splitFuncType' []         typeExpr              = return ([], typeExpr)
  splitFuncType' (_ : args) (HS.FuncType _ t1 t2) = do
    (argTypes, returnType) <- splitFuncType' args t2
    return (t1 : argTypes, returnType)
  splitFuncType' args@(arg : _) typeExpr = do
    typeExpr' <- expandTypeSynonym typeExpr
    if typeExpr /= typeExpr'
      then splitFuncType' args typeExpr'
      else
        reportFatal
        $  Message (HS.varPatSrcSpan arg) Error
        $  "Could not determine type of argument '"
        ++ HS.varPatIdent arg
        ++ "' for function '"
        ++ showPretty name
        ++ "'."

-------------------------------------------------------------------------------
-- Strongly connected components                                             --
-------------------------------------------------------------------------------

-- | Applies 'inferFuncDeclTypes' to the function declarations in the given
--   strongly connected components.
--
--   The given list of strongly connected components must be in recerse
--   topological order.
inferFuncDeclComponentTypes
  :: [DependencyComponent HS.FuncDecl]
  -> Converter [DependencyComponent HS.FuncDecl]
inferFuncDeclComponentTypes components = localEnv $ do
  ta <- inEnv makeTypeAssumption
  runTypeInference ta $ mapM inferFuncDeclComponentTypes' components

-- | Version of 'inferFuncDeclTypes' in the 'TypeInference' monad.
inferFuncDeclComponentTypes'
  :: DependencyComponent HS.FuncDecl
  -> TypeInference (DependencyComponent HS.FuncDecl)
inferFuncDeclComponentTypes' component = do
  component' <- mapComponentM inferFuncDeclTypes' component
  mapComponentM_ (mapM_ extendTypeAssumptionFor) component'
  return component'

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Tries to infer the types of (mutually recursive) function declarations.
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
    -- This required such that polymorphically recursive functions don't
    -- cause a type error.
  mapM_ extendTypeAssumptionFor funcDecls

  -- Add type annotations.
  --
  -- First we annotate all variable patterns, constructor and function
  -- applications as well as the return type of the function declarations
  -- with fresh type variables. The type variables act as placeholders for
  -- the actual types inferred below.
  annotatedFuncDecls <- liftConverter $ mapM annotateFuncDecl funcDecls

  -- Infer function types.
  --
  -- In addition to the actual type, we need the substitution computed
  -- during type inference. The substitution is applied to the function
  -- declarations in order to replace the fresh type variable placeholders
  -- added in the step above.
  (typeExprs, mgu)   <- inferFuncDeclTypes'' annotatedFuncDecls
  typedFuncDecls     <- liftConverter $ mapM (applySubst mgu) annotatedFuncDecls

  -- Abstract inferred type to type schema.
  --
  -- The function takes one type argument for each type variable in the
  -- inferred type expression. Additional type arguments that occur in
  -- type signatures and visible type applications on the right-hand side
  -- of the function but not in the inferred type (also known as "vanishing
  -- type  arguments") are added as well. The order of the type arguments
  -- depends on their order in the (type) expression (from left to right).
  let typeArgs = map typeVars typeExprs
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
  let funcNames           = map HS.funcDeclName abstractedFuncDecls
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
  mapM_ extendTypeAssumptionFor abstractedFuncDecls
  visiblyAppliedFuncDecls <- mapM applyFuncDeclVisibly abstractedFuncDecls

  -- Abstract new vanishing type arguments.
  --
  -- The instatiation of type schemas by 'applyFuncDeclVisibly' might
  -- have introduced new vanishing type arguments if a function with
  -- vanishing type arguments is applied that does not occur in the
  -- strongly connected component. Those additional type arguments
  -- need to be abstracted as well.
  liftConverter $ abstractVanishingTypeArgs visiblyAppliedFuncDecls

-- | Like 'inferFuncDeclTypes'' but does not abstract the type to a type
--   schema and returns the substitution.
inferFuncDeclTypes''
  :: [HS.FuncDecl] -> TypeInference ([HS.Type], Subst HS.Type)
inferFuncDeclTypes'' funcDecls = do
  (typedExprs, funcTypes) <- liftConverter
    $ mapAndUnzipM makeTypedExprs funcDecls
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
      funcExpr = HS.Var srcSpan funcName Nothing
      funcType = HS.funcType NoSrcSpan argTypes retType
      argExprs = map HS.varPatToExpr args'
      typedExprs =
        (funcExpr, funcType) : (rhs', retType) : zip argExprs argTypes
    return (typedExprs, funcType)
 where
  -- | Generates a fresh type variable for the given variable pattern or
  --   returns the annotated type variable.
  makeArgType :: HS.VarPat -> Converter HS.Type
  makeArgType = maybe freshTypeVar return . HS.varPatType

  -- | Generates a fresh type variable for the function declaration's return
  --   type or returns the annotated type variable.
  makeRetType :: Converter HS.Type
  makeRetType = maybe freshTypeVar return maybeRetType

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Tries to infer the type of the given expression from the current context
--   and abstracts it's type to a type schema.
--
--   The type of an expression @e@ is the same type inferred by
--   'inferFuncDeclTypes' for a function @f@ defined by @f = e@
--   where @f@ does not occur free in @e@.
--
--   Returns the inferred type schema and the expression where the
--   types of variable patterns and visible type applications have
--   been annotated.
inferExprType :: HS.Expr -> Converter (HS.Expr, HS.TypeSchema)
inferExprType expr = localEnv $ do
  funcIdent <- freshHaskellIdent freshFuncPrefix
  let funcDecl = HS.FuncDecl
        { HS.funcDeclSrcSpan    = NoSrcSpan
        , HS.funcDeclIdent      = HS.DeclIdent NoSrcSpan funcIdent
        , HS.funcDeclTypeArgs   = []
        , HS.funcDeclArgs       = []
        , HS.funcDeclRhs        = expr
        , HS.funcDeclReturnType = Nothing
        }
  [funcDecl'] <- inferFuncDeclTypes [funcDecl]
  return (HS.funcDeclRhs funcDecl', fromJust (HS.funcDeclTypeSchema funcDecl'))

-------------------------------------------------------------------------------
-- Type annotations                                                          --
-------------------------------------------------------------------------------

-- | Annotates the type of the given variable pattern using a fresh type
--   variable if there is no type annotation already.
annotateVarPat :: HS.VarPat -> Converter HS.VarPat
annotateVarPat (HS.VarPat srcSpan ident maybeVarType) = do
  typeVar <- maybe freshTypeVar return maybeVarType
  return (HS.VarPat srcSpan ident (Just typeVar))

-- | Annotates the given expression (a constructor or function application
--   or an error term) using a type signature and fresh type variable.
annotateWithTypeSig :: HS.Expr -> Converter HS.Expr
annotateWithTypeSig expr = do
  typeVar <- freshTypeVar
  let srcSpan = HS.exprSrcSpan expr
  return
    (HS.ExprTypeSig srcSpan expr (HS.TypeSchema srcSpan [] typeVar) Nothing)

-- | Adds fresh type variables to variable patterns in the given expression
--   and adds type signatures to constructor and function invocations as well
--   as error terms.
--
--   The fresh type variables are later replaced by the actual type
--   using the substitution computed during type inference.
annotateExpr :: HS.Expr -> Converter HS.Expr

-- Add type annotation to constructor and function invocations.
annotateExpr expr@(HS.Con _ _ _) = annotateWithTypeSig expr
annotateExpr expr@(HS.Var _ _ _) = annotateWithTypeSig expr

-- Add type annotation to error terms.
annotateExpr expr@(HS.Undefined _ _) = annotateWithTypeSig expr
annotateExpr expr@(HS.ErrorExpr _ _ _) = annotateWithTypeSig expr

-- There should be no visible type applications prior to type inference.
annotateExpr (HS.TypeAppExpr srcSpan _ _ _) = unexpectedTypeAppExpr srcSpan

-- Add visible type applications recursively.
annotateExpr (HS.App srcSpan e1 e2 exprType) = do
  e1' <- annotateExpr e1
  e2' <- annotateExpr e2
  return (HS.App srcSpan e1' e2' exprType)
annotateExpr (HS.If srcSpan e1 e2 e3 exprType) = do
  e1' <- annotateExpr e1
  e2' <- annotateExpr e2
  e3' <- annotateExpr e3
  return (HS.If srcSpan e1' e2' e3' exprType)
annotateExpr (HS.Case srcSpan expr alts exprType) = do
  expr' <- annotateExpr expr
  alts' <- mapM annotateAlt alts
  return (HS.Case srcSpan expr' alts' exprType)
annotateExpr (HS.Lambda srcSpan varPats expr exprType) = do
  varPats' <- mapM annotateVarPat varPats
  expr'    <- annotateExpr expr
  return (HS.Lambda srcSpan varPats' expr' exprType)
annotateExpr (HS.ExprTypeSig srcSpan expr typeSchema exprType) = do
  expr' <- annotateExpr expr
  return (HS.ExprTypeSig srcSpan expr' typeSchema exprType)
annotateExpr expr@(HS.IntLiteral _ _ _) = return expr

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
--   with fresh type variables if they are not annotated already.
annotateFuncDecl :: HS.FuncDecl -> Converter HS.FuncDecl
annotateFuncDecl (HS.FuncDecl srcSpan declIdent _ args rhs maybeRetType) = do
  args'   <- mapM annotateVarPat args
  rhs'    <- annotateExpr rhs
  retType <- maybe freshTypeVar return maybeRetType
  return (HS.FuncDecl srcSpan declIdent [] args' rhs' (Just retType))

-------------------------------------------------------------------------------
-- Visible type application                                                  --
-------------------------------------------------------------------------------

-- | Replaces a type signature added by 'annotateExpr' for a variable or
--   constructor with the given name by a visible type application of that
--   function or constructor.
applyVisibly :: HS.QName -> HS.Expr -> HS.Type -> TypeInference HS.Expr
applyVisibly name expr typeExpr = do
  maybeTypeSchema <- lookupTypeAssumption name
  case maybeTypeSchema of
    Nothing         -> return expr
    Just typeSchema -> do
      let srcSpan = HS.exprSrcSpan expr
      (typeExpr', typeArgs) <- liftConverter $ instantiateTypeSchema' typeSchema
      mgu <- liftConverter $ unifyOrFail srcSpan typeExpr typeExpr'
      fixed                 <- lookupFixedTypeArgs name
      typeArgs'             <- liftConverter
        $ mapM (applySubst mgu) (dropEnd (length fixed) typeArgs)
      return (HS.visibleTypeApp srcSpan expr (typeArgs' ++ fixed))

-- | Replaces the type signatures added by 'annotateExpr' by visible type
--   application expressions.
applyExprVisibly :: HS.Expr -> TypeInference HS.Expr

-- Add visible type applications to functions, constructors and error terms
-- with type annotation.
applyExprVisibly (HS.ExprTypeSig srcSpan expr (HS.TypeSchema _ [] typeExpr) _)
  | HS.Con _ conName _ <- expr = applyVisibly conName expr typeExpr
  | HS.Var _ varName _ <- expr = applyVisibly varName expr typeExpr
  | HS.Undefined _ _ <- expr = return
    (HS.TypeAppExpr srcSpan expr typeExpr Nothing)
  | HS.ErrorExpr _ _ _ <- expr = return
    (HS.TypeAppExpr srcSpan expr typeExpr Nothing)

-- There should be no visible type applications prior to type inference.
applyExprVisibly (HS.TypeAppExpr srcSpan _ _ _) = unexpectedTypeAppExpr srcSpan

-- Recursively add visible type applications.
applyExprVisibly (HS.ExprTypeSig srcSpan expr typeSchema exprType) = do
  expr' <- applyExprVisibly expr
  return (HS.ExprTypeSig srcSpan expr' typeSchema exprType)
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

-- Leave all other expressions unchanged.
applyExprVisibly expr@(HS.Con _ _ _       ) = return expr
applyExprVisibly expr@(HS.Var _ _ _       ) = return expr
applyExprVisibly expr@(HS.Undefined _ _   ) = return expr
applyExprVisibly expr@(HS.ErrorExpr  _ _ _) = return expr
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
    let typeArgNames = map (HS.UnQual . HS.Ident . HS.fromDeclIdent)
                           (HS.funcDeclTypeArgs funcDecl)
    abstractTypeArgs (typeArgNames ++ internalTypeArgNames) funcDecl

  -- | Adds visible type applications for 'internalTypeArgs' to recursive
  --   calls on the right-hand side of the given function declaration.
  addInternalTypeArgs :: HS.FuncDecl -> Converter HS.FuncDecl
  addInternalTypeArgs funcDecl = do
    modName <- inEnv envModName
    let funcNames    = map HS.funcDeclName funcDecls
        funcQNames = map HS.UnQual funcNames ++ map (HS.Qual modName) funcNames
        funcNameSet  = Set.fromList funcQNames
        funcNameSet' = withoutArgs (HS.funcDeclArgs funcDecl) funcNameSet
        rhs          = HS.funcDeclRhs funcDecl
        rhs'         = addInternalTypeArgsToExpr funcNameSet' rhs
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
  addInternalTypeArgsToExpr' funcNames (HS.ExprTypeSig srcSpan expr typeSchema exprType)
    = let expr' = addInternalTypeArgsToExpr funcNames expr
      in  (HS.ExprTypeSig srcSpan expr' typeSchema exprType, [])

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
-- Simplification of expression/type pairs                                   --
-------------------------------------------------------------------------------

-- | Simplifies expression/type pairs to variables/type pairs and type
--   equations.
simplifyTypedExpr :: HS.Expr -> HS.Type -> TypeInference ()

-- | If @C :: τ@ is a predefined constructor with @C :: forall α₀ … αₙ. τ'@,
--   then @τ = σ(τ')@ with @σ = { α₀ ↦ β₀, …, αₙ ↦ βₙ }@ where @β₀, …, βₙ@ are
--   new type variables.
simplifyTypedExpr (HS.Con srcSpan conName _) resType =
  addTypeEquationOrVarTypeFor srcSpan conName resType

-- | If @f :: τ@ is a predefined function with @f :: forall α₀ … αₙ. τ'@, then
--   @τ = σ(τ')@ with @σ = { α₀ ↦ β₀, …, αₙ ↦ βₙ }@ where @β₀, …, βₙ@ are new
--   type variables.
--   If @x :: τ@ is not a predefined function (i.e., a local variable or a
--   function whose type to infer), just remember that @x@ is of type @τ@.
simplifyTypedExpr (HS.Var srcSpan varName _) resType =
  addTypeEquationOrVarTypeFor srcSpan varName resType

-- If @(e₁ e₂) :: τ@, then @e₁ :: α -> τ@ and @e₂ :: α@ where @α@ is a new
-- type variable.
simplifyTypedExpr (HS.App _ e1 e2 _) resType = do
  argType <- liftConverter freshTypeVar
  simplifyTypedExpr e1 (HS.FuncType NoSrcSpan argType resType)
  simplifyTypedExpr e2 argType

-- There should be no visible type applications prior to type inference.
simplifyTypedExpr (HS.TypeAppExpr srcSpan _ _ _) _ =
  liftConverter $ unexpectedTypeAppExpr srcSpan

-- If @if e₁ then e₂ else e₃ :: τ@, then @e₁ :: Bool@ and @e₂, e₃ :: τ@.
simplifyTypedExpr (HS.If _ e1 e2 e3 _) resType = do
  let condType = HS.TypeCon NoSrcSpan HS.boolTypeConName
  simplifyTypedExpr e1 condType
  simplifyTypedExpr e2 resType
  simplifyTypedExpr e3 resType

-- If @case e of {p₀ -> e₀; …; pₙ -> eₙ} :: τ@, then @e₀, …, eₙ :: τ@ and
-- @e :: α@ and @p₀, …, pₙ :: α@ where @α@ is a new type variable.
simplifyTypedExpr (HS.Case _ expr alts _) resType = do
  exprType <- liftConverter freshTypeVar
  simplifyTypedExpr expr exprType
  mapM_ (\alt -> simplifyTypedAlt alt exprType resType) alts

-- Error terms are always typed correctly.
simplifyTypedExpr (HS.Undefined _ _  ) _ = return ()
simplifyTypedExpr (HS.ErrorExpr _ _ _) _ = return ()

-- If @n :: τ@ for some integer literal @n@, then @τ = Integer@.
simplifyTypedExpr (HS.IntLiteral srcSpan _ _) resType =
  addTypeEquation srcSpan (HS.TypeCon NoSrcSpan HS.integerTypeConName) resType

-- If @\x₀ … xₙ -> e :: τ@, then @x₀ :: α₀, … xₙ :: αₙ@ and @x :: β@ for new
-- type variables @α₀ … αₙ@ and @α₀ -> … -> αₙ -> β = τ@.
simplifyTypedExpr (HS.Lambda srcSpan args expr _) resType = do
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
simplifyTypedExpr (HS.ExprTypeSig srcSpan expr typeSchema _) resType = do
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
