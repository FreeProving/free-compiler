{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | This module contains functions for infering the type of expressions
--   and function declarations as well as functions for annotating the types
--   of variable patterns and adding visible applications for type arguments.

module Compiler.Analysis.TypeInference
  ( addTypeSigsToFuncDecls
  , inferFuncDeclTypes
  , inferExprType
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
makeTypeAssumtion :: Environment -> TypeAssumption
makeTypeAssumtion env = Map.fromList
  [ (name, typeSchema)
  | (scope, name) <- Map.keys (envEntries env)
  , scope == ValueScope
  , typeSchema <- maybeToList (lookupTypeSchema scope name env)
  ]

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

-- | Extends the type assumption with the type schema for the given function
--   declaration if all of its argument and return types are annotated.
extendTypeAssumptionFor :: HS.FuncDecl -> TypeInference ()
extendTypeAssumptionFor funcDecl = do
  let funcName = HS.funcDeclName funcDecl
  case HS.funcDeclTypeSchema funcDecl of
    Nothing         -> return ()
    Just typeSchema -> extendTypeAssumption funcName typeSchema

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
        name  = HS.UnQual (HS.funcDeclName funcDecl)
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
          ++ intercalate ", " (map (showPretty . HS.getSrcSpan) typeSchemas)

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
  splitFuncType' (_ : args) (HS.TypeFunc _ t1 t2) = do
    (argTypes, returnType) <- splitFuncType' args t2
    return (t1 : argTypes, returnType)
  splitFuncType' args@(arg : _) typeExpr = do
    typeExpr' <- expandTypeSynonym typeExpr
    if typeExpr /= typeExpr'
      then splitFuncType' args typeExpr'
      else
        reportFatal
        $  Message (HS.getSrcSpan arg) Error
        $  "Could not determine type of argument '"
        ++ HS.fromVarPat arg
        ++ "' for function '"
        ++ showPretty name
        ++ "'."

-- | Tries to infer the types of (mutually recursive) function declarations.
--
--   Returns the function declarations where the argument and return types
--   as well as the types of variable patterns on the right-hand side and
--   visible type arguments have been annotated with their inferred type.
inferFuncDeclTypes :: [HS.FuncDecl] -> Converter [HS.FuncDecl]
inferFuncDeclTypes funcDecls = localEnv $ do
  ta <- inEnv makeTypeAssumtion
  runTypeInference ta $ do
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
    (typeExprs, mgu) <- inferFuncDeclTypes' annotatedFuncDecls
    typedFuncDecls <- liftConverter $ mapM (applySubst mgu) annotatedFuncDecls

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
    -- TODO test this with (mutually) recursive functions that use functions
    --      with vanishing type arguments. Don't the newly abstracted type
    --      arguments have to be added to all function declarations and
    --      their visible type applications?
    liftConverter $ mapM abstractVanishingTypeArgs visiblyAppliedFuncDecls

-- | Like 'inferFuncDeclTypes' but does not abstract the type to a type
--   schema and returns the substitution.
inferFuncDeclTypes' :: [HS.FuncDecl] -> TypeInference ([HS.Type], Subst HS.Type)
inferFuncDeclTypes' funcDecls = do
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
      let srcSpan = HS.getSrcSpan expr
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
applyExprVisibly (HS.ExprTypeSig srcSpan expr (HS.TypeSchema _ [] typeExpr))
  | HS.Con _ conName <- expr = applyVisibly conName expr typeExpr
  | HS.Var _ varName <- expr = applyVisibly varName expr typeExpr
  | HS.Undefined _ <- expr   = return (HS.TypeAppExpr srcSpan expr typeExpr)
  | HS.ErrorExpr _ _ <- expr = return (HS.TypeAppExpr srcSpan expr typeExpr)

-- There should be no visible type applications prior to type inference.
applyExprVisibly (HS.TypeAppExpr srcSpan _ _) = unexpectedTypeAppExpr srcSpan

-- Recursively add visible type applications.
applyExprVisibly (HS.ExprTypeSig srcSpan expr typeSchema) = do
  expr' <- applyExprVisibly expr
  return (HS.ExprTypeSig srcSpan expr' typeSchema)
applyExprVisibly (HS.App srcSpan e1 e2) = do
  e1' <- applyExprVisibly e1
  e2' <- applyExprVisibly e2
  return (HS.App srcSpan e1' e2')
applyExprVisibly (HS.If srcSpan e1 e2 e3) = do
  e1' <- applyExprVisibly e1
  e2' <- applyExprVisibly e2
  e3' <- applyExprVisibly e3
  return (HS.If srcSpan e1' e2' e3')
applyExprVisibly (HS.Case srcSpan expr alts) = do
  expr' <- applyExprVisibly expr
  alts' <- mapM applyAltVisibly alts
  return (HS.Case srcSpan expr' alts')
applyExprVisibly (HS.Lambda srcSpan args expr) =
  removeVarPatsFromTypeAssumption args $ do
    expr' <- applyExprVisibly expr
    return (HS.Lambda srcSpan args expr')

-- Leave all other expressions unchanged.
applyExprVisibly expr@(HS.Con _ _       ) = return expr
applyExprVisibly expr@(HS.Var _ _       ) = return expr
applyExprVisibly expr@(HS.Undefined _   ) = return expr
applyExprVisibly expr@(HS.ErrorExpr  _ _) = return expr
applyExprVisibly expr@(HS.IntLiteral _ _) = return expr

-- | Applies 'applyExprVisibly' to the right-hand side of the given @case@-
--   expression alternative.
applyAltVisibly :: HS.Alt -> TypeInference HS.Alt
applyAltVisibly (HS.Alt srcSpan conPat varPats expr) =
  removeVarPatsFromTypeAssumption varPats $ do
    expr' <- applyExprVisibly expr
    return (HS.Alt srcSpan conPat varPats expr')

-- | Applies ' applyExprVisibly' to the right-hand side of the given function
--   declaration.
applyFuncDeclVisibly :: HS.FuncDecl -> TypeInference HS.FuncDecl
applyFuncDeclVisibly funcDecl = do
  let args = HS.funcDeclArgs funcDecl
      rhs  = HS.funcDeclRhs funcDecl
  removeVarPatsFromTypeAssumption args $ do
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
--   the given function declaration by renaming them to non-internal
--   type variables and adding them to the @forall@ quantifier of the
--   given type schema.
abstractVanishingTypeArgs :: HS.FuncDecl -> Converter HS.FuncDecl
abstractVanishingTypeArgs funcDecl = do
  let HS.TypeSchema _ typeArgs typeExpr =
        fromJust (HS.funcDeclTypeSchema funcDecl)
      typeArgNames = map (HS.UnQual . HS.Ident . HS.fromDeclIdent) typeArgs
      internalTypeArgNames = filter HS.isInternalQName (typeVars funcDecl)
  (HS.TypeSchema _ typeArgs' _, subst) <- abstractTypeSchema'
    (typeArgNames ++ internalTypeArgNames)
    typeExpr
  funcDecl' <- applySubst subst funcDecl
  return funcDecl' { HS.funcDeclTypeArgs = typeArgs' }

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
