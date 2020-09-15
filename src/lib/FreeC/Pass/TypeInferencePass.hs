{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module contains a compiler pass that infers the types of all
--   function declarations including the types of the sub-expressions of
--   their right-hand sides and type arguments to pass to used functions and
--   constructors.
--
--   = Examples
--
--   == Example 1: Type inference
--
--   The type of a function declaration that does not have a type signature
--
--   > double x = x + x
--
--   can be inferred from the types of the functions it is using on it's
--   right-hand side. Instead of just inferring the type of the declared
--   function, the types of all argument patterns and the return type of
--   the function are annotated by this pass.
--
--   > double (x :: Integer) :: Integer = x + x
--
--   == Example 2: Polymorphic functions
--
--   When a function is polymorphic
--
--   > null xs = case xs of {
--   >     []      -> False;
--   >     x : xs' -> True
--   >   }
--
--   its type variables will be specified explicitly on the left-hand
--   side of the function declaration. Their order depends on the order
--   in which they appear in the inferred type of the function. Type
--   arguments are listed from left to right.
--
--   > null @t0 (xs :: [t0]) :: Bool = case xs of {
--   >     []                        -> False;
--   >     (x :: t0) : (xs' :: [t0]) -> True
--   >   }
--
--   When such a polymorphic function is called
--
--   > null [1, 2, 3]
--
--   the type inference pass figures out the types the type arguments of
--   a function need to be instantiated with and inserts corresponding
--   visible type applications.
--
--   > null @Integer [1, 2, 3]
--
--   == Example 3: Vanishing type arguments
--
--   When type arguments are applied visibly, there are some cases where the
--   visible type application contains type variables that are not related to
--   the functions type (also called "vanishing type arguments"). The function
--   below has type @Bool@ for example, but the list it is using is polymorphic.
--
--   > myTrue = null []
--
--   Thus, the list contains elements of some type @t0@ which needs to be
--   added as a type argument to the list constructor @[]@ and @null@.
--
--   > myTrue @t0 :: Bool = null @t0 ([] @t0)
--
--   While Haskell would tolerate the definition of @myTrue@ without type
--   arguments, Coq does not accept an equivalent definition.
--
--   > Definition null {a : Type} (xs : list a) : bool
--   >   := match xs with
--   >      | nil      => true
--   >      | cons _ _ => false
--   >      end.
--   >
--   > Fail Definition myTrue := null nil.
--
--   > The command has indeed failed with message:
--   > Cannot infer the implicit parameter a of null whose type is "Type".
--
--   In order to fix this error, we have to do exactly what we did above, i.e.,
--   introduce a new type argument for @myTrue@ and pass that type argument
--   to either @null@, @nil@ or both.
--
--   > Definition myTrue (t0 : Type) := @null t0 (@nil t0).
--
--   We choose to pass all type arguments throughout the entire program
--   explicitly such that we can be sure, that Coq always agrees with the
--   types we have inferred.
--
--   == Example 4: Vanishing type arguments in recursive functions
--
--   When a recursive function contains vanishing type arguments (for
--   example, because it calls a function such as @true@ which introduces
--   a vanishing type argument),
--
--   > length xs = case xs of {
--   >     []      -> if true then 0 else 1
--   >     x : xs' -> 1 + length xs
--   >   }
--
--   the vanishing type arguments are passed unchanged to recursive calls
--   while regular type arguments (e.g., @t0@ below) could change in case
--   of polymorphic recursion.
--
--   > length @t0 @t1 (xs :: [t0]) :: Integer = case xs of {
--   >     []                        -> if true @t1 then 0 else 1
--   >     (x :: t0) : (xs' :: [t0]) -> 1 + length @t0 @t1 xs
--   >   }
--
--   If there are multiple sub-expressions that introduce vanishing type
--   arguments,
--
--   > if true && true then 0 else 1
--
--   the type arguments they introduce are distinct.
--
--   > if true @t1 && true @t2 then 0 else 1
--
--   Thus, @length@ would have two additional type arguments in this case.
--
--   > length @t0 @t1 @t2 (xs :: [t0]) :: Integer = {- ... -}
--
--   Note that vanishing type arguments are always listed after regular
--   type arguments and sorted by the order they occur on the right-hand
--   side from left to right.
--
--   == Example 5: Expression type annotations
--
--   In the examples above we've omitted type annotations of expressions
--   for better readability. However, in addition to variable patterns and
--   return types of functions, this pass also annotates all sub-expressions
--   on the right-hand side with the type that was inferred for them.
--
--   The type of an expression is stored in 'IR.exprTypeScheme' in the
--   form @'IR.TypeScheme' NoSrcSpan [] τ@ and can safely be accessed
--   via 'IR.exprType' after this pass. The field contains a type scheme
--   rather than a type because it is also used to store expression type
--   signatures of the user and type variables in type signatures need
--   to be universally quantified in Haskell.
--
--   = Specification
--
--   == Preconditions
--
--   * There are environment entries for all functions and constructors that
--     are used by functions in the strongly connected component (except
--     for the functions whose type to infer themselves).
--   * Type signatures have already been associated with the corresponding
--     function declarations (See "FreeC.Pass.TypeSignaturePass").
--
--   == Translation
--
--   The type inference algorithm implemented by the pass is based on the
--   algorithm by Damas and Milner (1982).
--
--   > [Damas & Milner, 1982]:
--   >   L. Damas and R. Milner. Principal type-schemes for functional programs.
--   >   In Proc. 9th Annual Symposium on Principles of Programming Languages,
--   >   pp. 207–212, 1982.
--
--   We are extending this algorithm to apply type arguments visibly and
--   make vanishing type arguments explicit.
--
--   See the comments in the definition of 'inferFuncDeclTypes'' for more
--   information on the actual implementation of type inference.
--
--   == Postconditions
--
--   * The types of all variable patterns, function return types and the types
--     of all expressions are explicitly annotated.
--   * All type arguments of all polymorphic functions and constructors are
--     applied visibly including vanishing type arguments.
module FreeC.Pass.TypeInferencePass ( typeInferencePass ) where

import           Control.Monad.Extra               ( zipWithM, zipWithM_ )
import           Control.Monad.Fail                ( MonadFail )
import           Control.Monad.State
  ( MonadState(..), StateT(..), evalStateT, gets, modify )
import           Data.Composition                  ( (.:) )
import           Data.List                         ( (\\), nub )
import           Data.List.Extra                   ( dropEnd, takeEnd )
import           Data.Map.Strict                   ( Map )
import qualified Data.Map.Strict                   as Map
import           Data.Maybe                        ( fromJust, maybeToList )
import           Data.Set                          ( Set )
import qualified Data.Set                          as Set

import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.Fresh
import qualified FreeC.IR.Base.Prelude             as IR.Prelude
import           FreeC.IR.DependencyGraph          ( mapComponentM )
import           FreeC.IR.Reference                ( freeTypeVars )
import           FreeC.IR.SrcSpan
import           FreeC.IR.Subst
import qualified FreeC.IR.Syntax                   as IR
import           FreeC.IR.TypeScheme
import           FreeC.IR.Unification
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pass.DependencyAnalysisPass
import           FreeC.Pretty

-- | A compiler pass that infers the types of (mutually recursive) function
--   declarations in the given strongly connected component of the function
--   dependency graph.
typeInferencePass :: DependencyAwarePass IR.FuncDecl
typeInferencePass = mapComponentM inferFuncDeclTypes

-------------------------------------------------------------------------------
-- Type Equations                                                            --
-------------------------------------------------------------------------------
-- | A type equation and the location in the source that caused the creation
--   of this type equation.
data TypeEquation = TypeEquation
  { eqnSrcSpan       :: SrcSpan
    -- ^ The location in the source code of the expression that caused the
    --   creation of this type equation.
  , eqnExpectedType  :: IR.Type
    -- ^ The left-hand side of the type equation.
  , eqnActualType    :: IR.Type
    -- ^ The right-hand side of the type equation.
  , eqnRigidTypeVars :: [IR.TypeVarDecl]
    -- ^ Declarations of type variables that are bound by the type signature
    --   of the function declaration that caused the creation of this type
    --   equation. These type variable must not be matched by the unification
    --   algorithm.
  }

-- | Type substitutions can be applied to the left- and right-hand sides of
--   type equations.
--
--   Rigid type variables in type equations cannot be substituted.
instance ApplySubst IR.Type TypeEquation where
  applySubst subst eqn
    = let subst'        = subst
          actualType'   = applySubst subst' (eqnActualType eqn)
          expectedType' = applySubst subst' (eqnExpectedType eqn)
      in eqn { eqnActualType = actualType', eqnExpectedType = expectedType' }

-------------------------------------------------------------------------------
-- Type Inference State Monad                                                --
-------------------------------------------------------------------------------
-- | Maps the names of defined functions and constructors to their type scheme.
type TypeAssumption = Map IR.QName IR.TypeScheme

-- | The state that is passed implicitly between the modules of this module.
data TypeInferenceState = TypeInferenceState
  { typeEquations  :: [TypeEquation]
    -- ^ The type equations that have to be unified.
  , rigidTypeVars  :: [IR.TypeVarDecl]
    -- ^ Declarations of type variables that are bound in the current context.
    --   This is used by 'annotateFuncDecls' to remember which type variables
    --   have to be inserted into 'eqnRigidTypeVars' by
    --   'addTypeEquation'.
  , typeAssumption :: TypeAssumption
    -- ^ The known type schemes of predefined functions and constructors.
  , fixedTypeArgs  :: Map IR.QName [IR.Type]
    -- ^ Maps function names to the types to instantiate their last type
    --   arguments with. This is used to instantiate additional type arguments
    --   in recursive functions correctly.
  }

-- | An empty 'TypeInferenceState'.
emptyTypeInferenceState :: TypeInferenceState
emptyTypeInferenceState = TypeInferenceState
  { typeEquations  = []
  , rigidTypeVars  = []
  , typeAssumption = Map.empty
  , fixedTypeArgs  = Map.empty
  }

-- | Creates a 'TypeAssumption' for all functions and constructors defined
--   in the given environment.
makeTypeAssumption :: Environment -> TypeAssumption
makeTypeAssumption env = Map.fromList
  [(name, typeScheme)
  | (scope, name) <- Map.keys (envEntries env)
  , scope == IR.ValueScope
  , typeScheme <- maybeToList (lookupTypeScheme scope name env)
  ]

-- | The state monad used throughout this module.
newtype TypeInference a = TypeInference
  { unwrapTypeInference :: StateT TypeInferenceState Converter a
  }
 deriving ( Functor, Applicative, Monad, MonadState TypeInferenceState
          , MonadFail )

-- | Messages can be reported during type inference.
instance MonadReporter TypeInference where
  liftReporter = liftConverter . liftReporter

-- | Lifts a converter into the type inference monad.
instance MonadConverter TypeInference where
  liftConverter = TypeInference . lift

-- | Runs the 'TypeInference' monad with the given initial type assumption.
runTypeInference :: TypeAssumption -> TypeInference a -> Converter a
runTypeInference initialTypeAssumption
  = flip evalStateT initialState . unwrapTypeInference
 where
  initialState :: TypeInferenceState
  initialState
    = emptyTypeInferenceState { typeAssumption = initialTypeAssumption }

-------------------------------------------------------------------------------
-- Type Inference Staten Inspection                                          --
-------------------------------------------------------------------------------
-- | Looks up the type scheme of the function or constructor with the given
--   name in the current type assumption.
lookupTypeAssumption :: IR.QName -> TypeInference (Maybe IR.TypeScheme)
lookupTypeAssumption name = gets (Map.lookup name . typeAssumption)

-- | Looks up the types to instantiate the additional type arguments
--   of the function with the given name with.
lookupFixedTypeArgs :: IR.QName -> TypeInference [IR.Type]
lookupFixedTypeArgs name = gets (Map.findWithDefault [] name . fixedTypeArgs)

-------------------------------------------------------------------------------
-- Type Inference State Manipulation                                         --
-------------------------------------------------------------------------------
-- | Adds a 'TypeEquation' entry the current state.
addTypeEquation :: SrcSpan -> IR.Type -> IR.Type -> TypeInference ()
addTypeEquation srcSpan t t' = modify $ \s ->
  let eqn = TypeEquation { eqnSrcSpan       = srcSpan
                         , eqnExpectedType  = t
                         , eqnActualType    = t'
                         , eqnRigidTypeVars = rigidTypeVars s
                         }
  in s { typeEquations = eqn : typeEquations s }

-- | Instantiates the type scheme of the function or constructor with the
--   given name and adds a 'TypeEquation' for the resulting type and the
--   given type to the current state.
--
--   If there is no entry for the given name, a fatal error is reported.
--   The error message refers to the given source location information.
addTypeEquationFor :: SrcSpan -> IR.QName -> IR.Type -> TypeInference ()
addTypeEquationFor srcSpan name resType = do
  maybeTypeScheme <- lookupTypeAssumption name
  case maybeTypeScheme of
    Nothing         -> reportFatal
      $ Message NoSrcSpan Error
      $ "Identifier not in scope " ++ showPretty name
    Just typeScheme -> do
      typeExpr <- liftConverter $ instantiateTypeScheme typeScheme
      addTypeEquation srcSpan typeExpr resType

-- | Extends the type assumption with the type scheme for the function,
--   constructor or local variable with the given name.
extendTypeAssumption :: IR.QName -> IR.TypeScheme -> TypeInference ()
extendTypeAssumption name typeScheme = modify $ \s ->
  s { typeAssumption = Map.insert name typeScheme (typeAssumption s) }

-- | Extends the type assumption with the type scheme for the given function
--   declaration if all of its argument and return types are annotated.
extendTypeAssumptionWithFuncDecl :: IR.FuncDecl -> TypeInference ()
extendTypeAssumptionWithFuncDecl funcDecl = mapM_
  (extendTypeAssumption (IR.funcDeclQName funcDecl))
  (IR.funcDeclTypeScheme funcDecl)

-- | Extends the type assumption with the unabstracted type the given
--   variable pattern has been annotated with.
extendTypeAssumptionWithVarPat :: IR.VarPat -> TypeInference ()
extendTypeAssumptionWithVarPat varPat = mapM_
  (extendTypeAssumption (IR.varPatQName varPat) . IR.TypeScheme NoSrcSpan [])
  (IR.varPatType varPat)

-- | Removes the variable bound by the given variable pattern from the
--   type assumption while running the given type inference.
removeVarPatFromTypeAssumption :: IR.VarPat -> TypeInference ()
removeVarPatFromTypeAssumption varPat = modify $ \s ->
  s { typeAssumption = Map.delete (IR.varPatQName varPat) (typeAssumption s) }

-- | Sets the types to instantiate additional type arguments of the function
--   with the given name with.
fixTypeArgs :: IR.QName -> [IR.Type] -> TypeInference ()
fixTypeArgs name subst = modify $ \s ->
  s { fixedTypeArgs = Map.insert name subst (fixedTypeArgs s) }

-------------------------------------------------------------------------------
-- Scoping                                                                   --
-------------------------------------------------------------------------------
-- | Runs the given type inference and discards all modifications of the
--   state afterwards.
withLocalState :: TypeInference a -> TypeInference a
withLocalState mx = do
  oldState <- get
  x <- mx
  put oldState
  return x

-- | Runs the given type inference and discards all modifications of the
--   type assumption afterwards.
withLocalTypeAssumption :: TypeInference a -> TypeInference a
withLocalTypeAssumption mx = do
  oldTypeAssumption <- gets typeAssumption
  x <- mx
  modify $ \s -> s { typeAssumption = oldTypeAssumption }
  return x

-- | Adds the given type variable declarations to the list of 'rigidTypeVars'
--   during the given type inference computation.
withRigidTypeVars :: [IR.TypeVarDecl] -> TypeInference a -> TypeInference a
withRigidTypeVars vs mx = do
  modify $ \s -> s { rigidTypeVars = vs ++ rigidTypeVars s }
  x <- mx
  modify $ \s -> s { rigidTypeVars = drop (length vs) (rigidTypeVars s) }
  return x

-------------------------------------------------------------------------------
-- Function Declarations                                                     --
-------------------------------------------------------------------------------
-- | Infers the types of (mutually recursive) function declarations.
--
--   Returns the function declarations where the argument and return types
--   as well as the types of variable patterns on the right-hand side and
--   visible type arguments have been annotated with their inferred type.
inferFuncDeclTypes :: [IR.FuncDecl] -> Converter [IR.FuncDecl]
inferFuncDeclTypes funcDecls = localEnv $ do
  ta <- inEnv makeTypeAssumption
  runTypeInference ta $ inferFuncDeclTypes' funcDecls

-- | Version of 'inferFuncDeclTypes' in the 'TypeInference' monad.
inferFuncDeclTypes' :: [IR.FuncDecl] -> TypeInference [IR.FuncDecl]
inferFuncDeclTypes' funcDecls = withLocalState $ do
  -- Add type assumption for functions with type signatures.
  --
  -- This is required such that polymorphically recursive functions don't
  -- cause a type error.
  mapM_ extendTypeAssumptionWithFuncDecl funcDecls
  -- Add type annotations.
  --
  -- In this step all variable patterns, return types and sub-expressions
  -- are annotated using fresh type variables. The type annotations resemble
  -- the structure of the actual type after this step already. For example,
  -- if @e₁ e₂@ is annotated with a type @τ@, then @e₂@ is annotated with
  -- a fresh type variable @α@ and @e₂@ is annotated with @α -> τ@.
  -- Furthermore, this step introduces type equations, for example if
  -- predefined functions and constructors are used.
  annotatedFuncDecls <- annotateFuncDecls funcDecls
  -- Unify type equations.
  --
  -- During the annotation of the function declaration, type equations were
  -- added. The system of type equations is solved by computing the most
  -- general unifier (mgu).
  --
  -- The mgu is then applied to the annotated function declarations to
  -- replace the type variables (that act as place holders) by their
  -- actual type. In the example of @e₁ e₂@ above for example, the type
  -- equation @α = Integer@ would have been added if @e₂@ was an integer
  -- literal. Thus, the mgu would map the type variable @α@ to @Integer@.
  -- By applying the mgu, the type annotation of @e₁ e₂@ is corrected to
  -- @Integer -> mgu(τ)@.
  eqns <- gets typeEquations
  mgu <- liftConverter $ unifyEquations eqns
  let typedFuncDecls = applySubst mgu annotatedFuncDecls
  -- Abstract inferred type to type scheme.
  --
  -- The function takes one type argument for each type variable in the
  -- inferred type expression. Additional type arguments that occur in
  -- type signatures and visible type applications on the right-hand side
  -- of the function but not in the inferred type (also known as "vanishing
  -- type  arguments") are added as well. The order of the type arguments
  -- depends on their order in the (type) expression (from left to right).
  let typeExprs           = map (fromJust . IR.funcDeclType) typedFuncDecls
      typeArgs            = map freeTypeVars typeExprs
      additionalTypeArgs  = nub (concatMap freeTypeVars typedFuncDecls)
        \\ concat typeArgs
      allTypeArgs         = map (++ additionalTypeArgs) typeArgs
      abstractedFuncDecls = zipWith abstractTypeArgs allTypeArgs typedFuncDecls
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
  let funcNames           = map IR.funcDeclQName abstractedFuncDecls
      additionalTypeArgs' = map (map IR.typeVarDeclToType
                                 . takeEnd (length additionalTypeArgs)
                                 . IR.funcDeclTypeArgs) abstractedFuncDecls
  zipWithM_ fixTypeArgs funcNames additionalTypeArgs'
  -- Add visible type applications.
  --
  -- Now that we also know the type arguments of the functions in then
  -- strongly connected component, we can replace the type annotations
  -- for function and constructor applications added by 'annotateFuncDecls'
  -- by visible type applications.
  mapM_ extendTypeAssumptionWithFuncDecl abstractedFuncDecls
  visiblyAppliedFuncDecls <- mapM applyFuncDeclVisibly abstractedFuncDecls
  -- Abstract new vanishing type arguments.
  --
  -- The instantiation of type schemes by 'applyFuncDeclVisibly' might
  -- have introduced new vanishing type arguments if a function with
  -- vanishing type arguments is applied that does not occur in the
  -- strongly connected component. Those additional type arguments
  -- need to be abstracted as well.
  return (abstractVanishingTypeArgs visiblyAppliedFuncDecls)

-------------------------------------------------------------------------------
-- Type Annotations                                                          --
-------------------------------------------------------------------------------
-- | Generates a fresh type variable if the given type is @Nothing@
--   and returns the given type otherwise.
maybeFreshTypeVar :: Maybe IR.Type -> TypeInference IR.Type
maybeFreshTypeVar = liftConverter . maybe freshTypeVar return

-- | Annotates the type of the given variable pattern using a fresh type
--   variable if there is no type annotation already and extends the type
--   assumption by the (unabstracted) type for the declared variable.
annotateVarPat :: IR.VarPat -> TypeInference IR.VarPat
annotateVarPat varPat = do
  varPatType' <- maybeFreshTypeVar (IR.varPatType varPat)
  let varPat' = varPat { IR.varPatType = Just varPatType' }
  extendTypeAssumptionWithVarPat varPat'
  return varPat'

-- | Annotates the given expression with the given type if it does not have
--   a type annotation already and annotates the expression recursively.
--
--   If the type (or the general structure of the type) of the given expression
--   is known, type equations are added. For example, if a function is
--   predefined, it is known that its type must be an instance of its type
--   scheme. Thus, the type scheme is instantiated with fresh type variables
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
annotateExprWith :: IR.Expr -> IR.Type -> TypeInference IR.Expr
annotateExprWith expr resType = case IR.exprTypeScheme expr of
  Nothing         -> annotateExprWith' expr resType
  Just typeScheme -> do
    exprType <- liftConverter $ instantiateTypeScheme typeScheme
    addTypeEquation (IR.exprSrcSpan expr) exprType resType
    annotateExprWith' expr exprType

-- | Version of 'annotateExprWith' that ignores existing type annotations.
annotateExprWith' :: IR.Expr -> IR.Type -> TypeInference IR.Expr

-- If @C :: τ@ is a predefined constructor with @C :: forall α₀ … αₙ. τ'@,
-- then add a type equation @σ(τ') = τ@ where @σ = { α₀ ↦ β₀, …, αₙ ↦ βₙ }@
-- and @β₀, …, βₙ@ are fresh type variables.
annotateExprWith' (IR.Con srcSpan conName _) resType = do
  addTypeEquationFor srcSpan conName resType
  return (IR.Con srcSpan conName (makeExprType resType))
-- If @x :: τ@ is in scope with @x :: forall α₀ … αₙ. τ'@, then add a type
-- equation @σ(τ') = τ@ where @σ = { α₀ ↦ β₀, …, αₙ ↦ βₙ }@ and @β₀, …, βₙ@
-- are fresh type variables.
-- In case of local variables or functions whose types are currently inferred,
-- the type assumption of @x@ is not abstracted (i.e., @n = 0@).
-- Therefore a type equation that unifies the type the binder of @x@ has been
-- annotated with and the given type @τ@ is simply added in this case.
annotateExprWith' (IR.Var srcSpan varName _) resType = do
  addTypeEquationFor srcSpan varName resType
  return (IR.Var srcSpan varName (makeExprType resType))
-- If @(e₁ e₂) :: τ@, then @e₁ :: α -> τ@ and @e₂ :: α@ where @α@ is a fresh
-- type variable.
annotateExprWith' (IR.App srcSpan e1 e2 _) resType = do
  argType <- liftConverter freshTypeVar
  e1' <- annotateExprWith e1 (IR.FuncType NoSrcSpan argType resType)
  e2' <- annotateExprWith e2 argType
  return (IR.App srcSpan e1' e2' (makeExprType resType))
-- There should be no visible type applications prior to type inference.
annotateExprWith' (IR.TypeAppExpr srcSpan _ _ _) _
  = unexpectedTypeAppExpr srcSpan
-- If @if e₁ then e₂ else e₃ :: τ@, then @e₁ :: Bool@ and @e₂, e₃ :: τ@.
annotateExprWith' (IR.If srcSpan e1 e2 e3 _) resType = do
  let condType = IR.TypeCon NoSrcSpan IR.Prelude.boolTypeConName
  e1' <- annotateExprWith e1 condType
  e2' <- annotateExprWith e2 resType
  e3' <- annotateExprWith e3 resType
  return (IR.If srcSpan e1' e2' e3' (makeExprType resType))
-- If @case e of {p₀ -> e₀; …; pₙ -> eₙ} :: τ@, then @e₀, …, eₙ :: τ@ and
-- @e :: α@ and @p₀, …, pₙ :: α@ where @α@ is a fresh type variable.
annotateExprWith' (IR.Case srcSpan scrutinee alts _) resType = do
  scrutineeType <- liftConverter freshTypeVar
  scrutinee' <- annotateExprWith scrutinee scrutineeType
  alts' <- mapM (flip annotateAlt scrutineeType) alts
  return (IR.Case srcSpan scrutinee' alts' (makeExprType resType))
 where
  -- | Annotates the pattern of the given alternative with the given type
  --   and its right-hand side with the @case@ expressions result type.
  annotateAlt :: IR.Alt -> IR.Type -> TypeInference IR.Alt
  annotateAlt (IR.Alt altSrcSpan conPat varPats rhs) patType
    = withLocalTypeAssumption $ do
      varPats' <- mapM annotateVarPat varPats
      let varPatTypes = map (fromJust . IR.varPatType) varPats'
          conPatType  = IR.funcType NoSrcSpan varPatTypes patType
      addTypeEquationFor altSrcSpan (IR.conPatName conPat) conPatType
      rhs' <- annotateExprWith rhs resType
      return (IR.Alt altSrcSpan conPat varPats' rhs')
-- Error terms are predefined polymorphic functions. They can be annotated
-- with the given result type directly.
annotateExprWith' (IR.Undefined srcSpan _) resType = return
  (IR.Undefined srcSpan (makeExprType resType))
annotateExprWith' (IR.ErrorExpr srcSpan msg _) resType = return
  (IR.ErrorExpr srcSpan msg (makeExprType resType))
-- The @trace@ effect is applied to an expression and has the same type as the
-- traced expression.
annotateExprWith' (IR.Trace srcSpan msg expr _) resType = do
  expr' <- annotateExprWith' expr resType
  return (IR.Trace srcSpan msg expr' (makeExprType resType))
-- If @n :: τ@ for some integer literal @n@, then add the type equation
-- @Integer = τ@.
annotateExprWith' (IR.IntLiteral srcSpan value _) resType = do
  let intType = IR.TypeCon NoSrcSpan IR.Prelude.integerTypeConName
  addTypeEquation srcSpan intType resType
  return (IR.IntLiteral srcSpan value (makeExprType resType))
-- If @\\x₀ … xₙ -> e :: τ@, then @x₀ :: α₀, …, xₙ :: αₙ@ and @x :: β@ for
-- fresh type variables @α₀, …, αₙ@ and @β@ and add the a type equation
-- @α₀ -> … -> αₙ -> β = τ@.
annotateExprWith' (IR.Lambda srcSpan args expr _) resType
  = withLocalTypeAssumption $ do
    args' <- mapM annotateVarPat args
    retType <- liftConverter freshTypeVar
    expr' <- annotateExprWith expr retType
    let argTypes = map (fromJust . IR.varPatType) args'
        funcType = IR.funcType NoSrcSpan argTypes retType
    addTypeEquation srcSpan funcType resType
    return (IR.Lambda srcSpan args' expr' (makeExprType resType))
annotateExprWith' (IR.Let srcSpan binds expr _) resType
  = withLocalTypeAssumption $ do
    bindVarPats' <- mapM (annotateVarPat . IR.bindVarPat) binds
    exprType <- liftConverter freshTypeVar
    binds'' <- zipWithM annotateBindExpr binds bindVarPats'
    expr' <- annotateExprWith expr exprType
    return (IR.Let srcSpan binds'' expr' (makeExprType resType))
 where
  annotateBindExpr :: IR.Bind -> IR.VarPat -> TypeInference IR.Bind
  annotateBindExpr (IR.Bind bindSrcSpan _ bindExpr) bindVarPat' = do
    let Just bindType = IR.varPatType bindVarPat'
    bindExpr' <- annotateExprWith bindExpr bindType
    return (IR.Bind bindSrcSpan bindVarPat' bindExpr')

-- | Utility function used by 'annotateExprWith' to construct the
--   'IR.exprTypeScheme' field.
--
--   Never returns @Nothing@ since all expressions must be annotated by
--   'annotateExprWith'. The type scheme does not quantify any variables.
--   Type variables will be bound by the function declaration that contains
--   the expression.
makeExprType :: IR.Type -> Maybe IR.TypeScheme
makeExprType = Just . IR.TypeScheme NoSrcSpan []

-- | Annotates the function arguments and return types with fresh type
--   variables if they are not annotated already and applies 'annotateExprWith'
--   to the right-hand side of the given function declaration with the
--   return type of the function.
annotateFuncDecls :: [IR.FuncDecl] -> TypeInference [IR.FuncDecl]
annotateFuncDecls funcDecls = withLocalTypeAssumption $ do
  funcDecls' <- mapM annotateFuncDeclLhs funcDecls
  mapM_ extendTypeAssumptionWithFuncDecl funcDecls'
  mapM annotateFuncDeclRhs funcDecls'
 where
  -- | Annotates the argument and return types of the given function
  --   declaration.
  annotateFuncDeclLhs :: IR.FuncDecl -> TypeInference IR.FuncDecl
  annotateFuncDeclLhs funcDecl = withLocalTypeAssumption $ do
    args' <- mapM annotateVarPat (IR.funcDeclArgs funcDecl)
    retType <- maybeFreshTypeVar (IR.funcDeclReturnType funcDecl)
    return funcDecl { IR.funcDeclArgs       = args'
                    , IR.funcDeclReturnType = Just retType
                    }

  -- | Annotates the right-hand side of the given function declaration.
  annotateFuncDeclRhs :: IR.FuncDecl -> TypeInference IR.FuncDecl
  annotateFuncDeclRhs funcDecl = withLocalTypeAssumption
    $ withRigidTypeVars (IR.funcDeclTypeArgs funcDecl)
    $ do
      let Just retType = IR.funcDeclReturnType funcDecl
      mapM_ extendTypeAssumptionWithVarPat (IR.funcDeclArgs funcDecl)
      rhs' <- annotateExprWith (IR.funcDeclRhs funcDecl) retType
      return funcDecl { IR.funcDeclRhs = rhs' }

-------------------------------------------------------------------------------
-- Visible Type Application                                                  --
-------------------------------------------------------------------------------
-- | Adds visible type application expressions to a function or constructor
--   with the given name.
--
--   Unifies the type annotations added by 'annotateExprWith' and the assumed
--   type scheme for the function or constructor to infer the type arguments.
--   If the function or constructor has vanishing type arguments, this function
--   introduces new vanishing type variables to the expression that have to be
--   abstracted later (See 'abstractVanishingTypeArgs').
--
--   Since the expression has been annotated with 'annotateExprWith', we
--   can safely assume, that 'IR.exprTypeScheme' does not quantify any type
--   variables itself.
applyVisibly :: IR.QName -> IR.Expr -> TypeInference IR.Expr
applyVisibly name expr = do
  let srcSpan            = IR.exprSrcSpan expr
      Just annotatedType = IR.exprType expr
  maybeAssumedTypeScheme <- lookupTypeAssumption name
  case maybeAssumedTypeScheme of
    Nothing                -> return expr
    Just assumedTypeScheme -> do
      (assumedType, typeArgs)
        <- liftConverter $ instantiateTypeScheme' assumedTypeScheme
      mgu <- liftConverter $ unifyOrFail srcSpan annotatedType assumedType
      fixed <- lookupFixedTypeArgs name
      let typeArgs' = applySubst mgu (dropEnd (length fixed) typeArgs)
      return (IR.visibleTypeApp srcSpan expr (typeArgs' ++ fixed))

-- | Adds visible type application expressions to function and constructor
--   applications in the given expression.
applyExprVisibly :: IR.Expr -> TypeInference IR.Expr

-- Add visible type applications to functions, constructors and effect terms.
-- We can assume that the expression has a type annotation without quantified
-- type variables since 'annotateExprWith' was applied before.
applyExprVisibly expr@(IR.Con _ conName _)
  = applyVisibly conName expr
applyExprVisibly expr@(IR.Var _ varName _)
  = applyVisibly varName expr
applyExprVisibly expr@(IR.Undefined srcSpan exprType)   = do
  let Just (IR.TypeScheme _ [] typeArg) = exprType
  return (IR.TypeAppExpr srcSpan expr typeArg exprType)
applyExprVisibly expr@(IR.ErrorExpr srcSpan _ exprType) = do
  let Just (IR.TypeScheme _ [] typeArg) = exprType
  return (IR.TypeAppExpr srcSpan expr typeArg exprType)
applyExprVisibly (IR.Trace srcSpan msg e exprType) = do
  e' <- applyExprVisibly e
  let Just (IR.TypeScheme _ [] typeArg) = exprType
      expr' = IR.Trace srcSpan msg e' exprType
  return (IR.TypeAppExpr srcSpan expr' typeArg exprType)
-- There should be no visible type applications prior to type inference.
applyExprVisibly (IR.TypeAppExpr srcSpan _ _ _)
  = unexpectedTypeAppExpr srcSpan
-- Recursively add visible type applications.
applyExprVisibly (IR.App srcSpan e1 e2 exprType)        = do
  e1' <- applyExprVisibly e1
  e2' <- applyExprVisibly e2
  return (IR.App srcSpan e1' e2' exprType)
applyExprVisibly (IR.If srcSpan e1 e2 e3 exprType)      = do
  e1' <- applyExprVisibly e1
  e2' <- applyExprVisibly e2
  e3' <- applyExprVisibly e3
  return (IR.If srcSpan e1' e2' e3' exprType)
applyExprVisibly (IR.Case srcSpan expr alts exprType)   = do
  expr' <- applyExprVisibly expr
  alts' <- mapM applyAltVisibly alts
  return (IR.Case srcSpan expr' alts' exprType)
applyExprVisibly (IR.Let srcSpan binds expr exprType)   = do
  binds' <- mapM applyBindVisibly binds
  expr' <- applyExprVisibly expr
  return (IR.Let srcSpan binds' expr' exprType)
applyExprVisibly (IR.Lambda srcSpan args expr exprType)
  = withLocalTypeAssumption $ do
    mapM_ removeVarPatFromTypeAssumption args
    expr' <- applyExprVisibly expr
    return (IR.Lambda srcSpan args expr' exprType)
-- Leave all literals unchanged.
applyExprVisibly expr@(IR.IntLiteral _ _ _)             = return expr

-- | Applies 'applyExprVisibly' to the right-hand side of the given let binding.
applyBindVisibly :: IR.Bind -> TypeInference IR.Bind
applyBindVisibly (IR.Bind srcSpan varPat expr) = do
  expr' <- applyExprVisibly expr
  return (IR.Bind srcSpan varPat expr')

-- | Applies 'applyExprVisibly' to the right-hand side of the given @case@-
--   expression alternative.
applyAltVisibly :: IR.Alt -> TypeInference IR.Alt
applyAltVisibly (IR.Alt srcSpan conPat varPats expr)
  = withLocalTypeAssumption $ do
    mapM_ removeVarPatFromTypeAssumption varPats
    expr' <- applyExprVisibly expr
    return (IR.Alt srcSpan conPat varPats expr')

-- | Applies ' applyExprVisibly' to the right-hand side of the given function
--   declaration.
applyFuncDeclVisibly :: IR.FuncDecl -> TypeInference IR.FuncDecl
applyFuncDeclVisibly funcDecl = withLocalTypeAssumption $ do
  let args = IR.funcDeclArgs funcDecl
      rhs  = IR.funcDeclRhs funcDecl
  mapM_ removeVarPatFromTypeAssumption args
  rhs' <- applyExprVisibly rhs
  return funcDecl { IR.funcDeclRhs = rhs' }

-------------------------------------------------------------------------------
-- Abstracting Type Arguments                                                --
-------------------------------------------------------------------------------
-- | Normalizes the names of the given type variables and adds them as type
--   arguments to the function declaration.
--
--   The first argument contains the names of type variables that should be
--   bound by type arguments. Usually these are the type variables that
--   occur in the function declaration's type and on its right-hand side.
--
--   Fresh type variables used by the given type are replaced by regular type
--   variables with the prefix 'freshTypeArgPrefix'. All other type variables
--   are not renamed.
abstractTypeArgs :: [IR.TypeVarIdent] -> IR.FuncDecl -> IR.FuncDecl
abstractTypeArgs typeArgIdents funcDecl
  = let typeArgs = map (IR.UnQual . IR.Ident) typeArgIdents
        IR.TypeScheme _ _ typeExpr = fromJust (IR.funcDeclTypeScheme funcDecl)
        (IR.TypeScheme _ typeArgs' _, subst)
          = abstractTypeScheme' typeArgs typeExpr
        funcDecl' = applySubst subst funcDecl
    in funcDecl' { IR.funcDeclTypeArgs = typeArgs' }

-- | Abstracts the remaining internal type variables that occur within
--   the given function declarations by renaming them to non-internal
--   type variables and adding them as type arguments to the function
--   declarations.
--
--   The added type arguments are also added as visible type applications
--   to recursive calls to the function declarations.
abstractVanishingTypeArgs :: [IR.FuncDecl] -> [IR.FuncDecl]
abstractVanishingTypeArgs funcDecls
  = let funcDecls' = map addInternalTypeArgs funcDecls
    in map abstractVanishingTypeArgs' funcDecls'
 where
  -- | The names of the type variables to abstract.
  internalTypeArgIdents :: [IR.TypeVarIdent]
  internalTypeArgIdents = filter IR.isInternalIdent (freeTypeVars funcDecls)

  -- | Type variables for 'internalTypeArgNames'.
  internalTypeArgs :: [IR.Type]
  internalTypeArgs = map (IR.TypeVar NoSrcSpan) internalTypeArgIdents

  -- | Renames 'internalTypeArgNames' and adds them as type arguments
  --   to the given function declaration.
  abstractVanishingTypeArgs' :: IR.FuncDecl -> IR.FuncDecl
  abstractVanishingTypeArgs' funcDecl
    = let typeArgIdents = map IR.typeVarDeclIdent (IR.funcDeclTypeArgs funcDecl)
      in abstractTypeArgs (typeArgIdents ++ internalTypeArgIdents) funcDecl

  -- | Adds visible type applications for 'internalTypeArgs' to recursive
  --   calls on the right-hand side of the given function declaration.
  addInternalTypeArgs :: IR.FuncDecl -> IR.FuncDecl
  addInternalTypeArgs funcDecl
    = let funcNames  = Set.fromList (map IR.funcDeclQName funcDecls)
          funcNames' = withoutArgs (IR.funcDeclArgs funcDecl) funcNames
          rhs        = IR.funcDeclRhs funcDecl
          rhs'       = addInternalTypeArgsToExpr funcNames' rhs
      in funcDecl { IR.funcDeclRhs = rhs' }

  -- | Adds visible type applications for 'internalTypeArgs' to recursive
  --   calls in the given expression.
  addInternalTypeArgsToExpr :: Set IR.QName -> IR.Expr -> IR.Expr
  addInternalTypeArgsToExpr = uncurry (IR.visibleTypeApp NoSrcSpan)
    .: addInternalTypeArgsToExpr'

  -- | Like 'addInternalTypeArgs' but returns the visible type
  --   arguments that still need to be added.
  addInternalTypeArgsToExpr' :: Set IR.QName -> IR.Expr -> (IR.Expr, [IR.Type])

  -- If this is a recursive call the internal type arguments need to be
  -- applied visibly.
  addInternalTypeArgsToExpr' funcNames expr@(IR.Var _ varName _)
    | varName `Set.member` funcNames = (expr, internalTypeArgs)
    | otherwise = (expr, [])
  -- Add new type arguments after existing visible type applications.
  addInternalTypeArgsToExpr' funcNames
    (IR.TypeAppExpr srcSpan expr typeExpr exprType)
    = let (expr', typeArgs) = addInternalTypeArgsToExpr' funcNames expr
      in (IR.TypeAppExpr srcSpan expr' typeExpr exprType, typeArgs)
  -- Recursively add the internal type arguments.
  addInternalTypeArgsToExpr' funcNames (IR.App srcSpan e1 e2 exprType)
    = let e1' = addInternalTypeArgsToExpr funcNames e1
          e2' = addInternalTypeArgsToExpr funcNames e2
      in (IR.App srcSpan e1' e2' exprType, [])
  addInternalTypeArgsToExpr' funcNames (IR.If srcSpan e1 e2 e3 exprType)
    = let e1' = addInternalTypeArgsToExpr funcNames e1
          e2' = addInternalTypeArgsToExpr funcNames e2
          e3' = addInternalTypeArgsToExpr funcNames e3
      in (IR.If srcSpan e1' e2' e3' exprType, [])
  addInternalTypeArgsToExpr' funcNames (IR.Case srcSpan expr alts exprType)
    = let expr' = addInternalTypeArgsToExpr funcNames expr
          alts' = map (addInternalTypeArgsToAlt funcNames) alts
      in (IR.Case srcSpan expr' alts' exprType, [])
  addInternalTypeArgsToExpr' funcNames (IR.Lambda srcSpan args expr exprType)
    = let funcNames' = withoutArgs args funcNames
          expr'      = addInternalTypeArgsToExpr funcNames' expr
      in (IR.Lambda srcSpan args expr' exprType, [])
  addInternalTypeArgsToExpr' funcNames (IR.Let srcSpan binds expr exprType)
    = let funcNames' = withoutArgs (map IR.bindVarPat binds) funcNames
          expr'      = addInternalTypeArgsToExpr funcNames' expr
      in (IR.Let srcSpan binds expr' exprType, [])
  addInternalTypeArgsToExpr' funcNames (IR.Trace srcSpan msg expr exprType)
    = let expr' = addInternalTypeArgsToExpr funcNames expr
      in (IR.Trace srcSpan msg expr' exprType, [])
  -- Leave all other expressions unchanged.
  addInternalTypeArgsToExpr' _ expr@(IR.Con _ _ _) = (expr, [])
  addInternalTypeArgsToExpr' _ expr@(IR.IntLiteral _ _ _) = (expr, [])
  addInternalTypeArgsToExpr' _ expr@(IR.Undefined _ _) = (expr, [])
  addInternalTypeArgsToExpr' _ expr@(IR.ErrorExpr _ _ _) = (expr, [])

  -- | Applies 'addInternalTypeArgsToExpr' to the right-hand side of
  --   the given @case@ expression alternative.
  addInternalTypeArgsToAlt :: Set IR.QName -> IR.Alt -> IR.Alt
  addInternalTypeArgsToAlt funcNames (IR.Alt srcSpan conPat varPats expr)
    = let funcNames' = withoutArgs varPats funcNames
          expr'      = addInternalTypeArgsToExpr funcNames' expr
      in IR.Alt srcSpan conPat varPats expr'

  -- | Removes the names of the given variable patterns from the given set.
  withoutArgs :: [IR.VarPat] -> Set IR.QName -> Set IR.QName
  withoutArgs = flip (Set.\\) . Set.fromList . map IR.varPatQName

-------------------------------------------------------------------------------
-- Solving Type Equations                                                    --
-------------------------------------------------------------------------------
-- | Finds the most general unifier that satisfies all given type equations.
--
--   The type equations are unified in reverse order in order to improve
--   error messages. The list of type equations contains equations for
--   parent expressions before sub-expressions. By reversing the order of
--   equations, type errors in sub-expressions are reported first.
unifyEquations :: [TypeEquation] -> Converter (Subst IR.Type)
unifyEquations = unifyEquations' identitySubst . reverse
 where
  unifyEquations'
    :: Subst IR.Type -> [TypeEquation] -> Converter (Subst IR.Type)
  unifyEquations' subst []           = return subst
  unifyEquations' subst (eqn : eqns) = do
    let eqn' = applySubst subst eqn
    mgu <- unifyEquation eqn'
    let subst' = composeSubst mgu subst
    unifyEquations' subst' eqns

-- | Unifies the left- and right-hand sides of the given type equation.
--
--   In order to avoid matching of rigid type variables that are bound by
--   type signatures, the unification algorithm checks whether there is an
--   environment entry for a matched type variable. Thus, we have to insert
--   such entries for the type variables bound by the function declaration
--   that created the given type equation before the actual unification.
--   These entries are inserted only locally and not visible after this
--   operation anymore.
unifyEquation :: TypeEquation -> Converter (Subst IR.Type)
unifyEquation eqn = localEnv $ do
  mapM_ bindRigidTypeVar (eqnRigidTypeVars eqn)
  unifyOrFail (eqnSrcSpan eqn) (eqnExpectedType eqn) (eqnActualType eqn)

-------------------------------------------------------------------------------
-- Rigid Type Variables                                                      --
-------------------------------------------------------------------------------
-- | Adds an environment entry for the type variable that is bound by the
--   given type variable declaration.
bindRigidTypeVar :: MonadConverter m => IR.TypeVarDecl -> m ()
bindRigidTypeVar typeVarDecl = modifyEnv
  $ addEntry
  $ TypeVarEntry
  { entrySrcSpan   = IR.typeVarDeclSrcSpan typeVarDecl
  , entryName      = IR.UnQual (IR.Ident (IR.typeVarDeclIdent typeVarDecl))
  , entryIdent     = undefined
  , entryAgdaIdent = undefined
  }

-------------------------------------------------------------------------------
-- Error Reporting                                                           --
-------------------------------------------------------------------------------
-- | Reports an internal error when a type application expression is
--   encountered prior to type inference.
unexpectedTypeAppExpr :: MonadReporter r => SrcSpan -> r a
unexpectedTypeAppExpr srcSpan = reportFatal
  $ Message srcSpan Internal
  $ "Unexpected visible type application."
