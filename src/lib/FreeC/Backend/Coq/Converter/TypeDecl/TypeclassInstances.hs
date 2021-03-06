-- | This module contains functions to generate instances for supported
--   typeclasses for user-defined Haskell data types.
--
--   Suppose we have a type
--   > data T α₁ … αₙ = C₁ τ₍₁,₁₎ … τ₍₁,ₘ₁₎ | … | Cₖ τ₍ₖ,₁₎ … τ₍ₖ,ₘₖ₎.
--   We wish to generate an instance of class @C@ providing the function
--   @f : T α₁ … αₙ -> τ@, where @τ@ is a type.
--   For example, for the @Normalform@ class, @f@ would be
--   > nf' : T α₁ … αₙ -> Free Shape Pos (T α₁ … αₙ).
--
--   The generated function has the following basic structure:
--
--   > f'T < class-specific binders > (x : T α₁ … αₙ) : B
--   >      := match x with
--   >         | C₁ fx₍₁,₁₎ … fx₍₁,ₘ₁₎ => < buildValue x [fx₍₁,₁₎, …, fx₍₁,ₘ₁₎ >
--   >         | …
--   >         | Cₖ fx₍ₖ,₁₎ … fx₍ₖ,ₘₖ₎ => < buildValue x [fx₍ₖ,₁₎, …, fxk₍ₖ,ₘₖ₎] >
--   >         end.
--
--   @buildValue x [fx₍ᵢ,₁₎, …, fx₍ᵢ,ₘᵢ₎]@ represents class-specific code that
--   actually constructs a value of type @τ@ when given @x@ and the
--   constructor's parameters as arguments.
--
--   For example, for a @Normalform@ instance of a type
--   @data List a = Nil | Cons a (List a)@,
--   the function would look as follows.
--
--   > nf'List_ {Shape : Type} {Pos : Shape -> Type}
--   >          {a b : Type} `{Normalform Shape Pos a b}
--   >          (x : List Shape Pos a)
--   >   : Free Shape Pos (List Identity.Shape Identity.Pos b)
--   >      := match x with
--   >         | nil => pure nil
--   >         | cons fx_0 fx_1 => nf fx_0 >>= fun nx_0 =>
--   >                             fx_1 >>= fun x_1 =>
--   >                             nf'List x_1 >>= fun nx_1 =>
--   >                             pure (cons (pure nx_0) (pure nx_1))
--   >         end.
--
--   Typically, @buildValue@ will use the class function @f@ on all components,
--   then reconstruct the value using the results of those function calls.
--   In the example above, we use @nf@ on @fx_0@ of type @a@. @nf fx_0@ means
--   the same as @fx_0 >>= fun x_0 => nf' x_0@.
--
--   Since we translate types in topological order and @C@ instances exist for
--   all previously translated types (and types from the Prelude), we can use
--   @f@ on most arguments.
--   For all type variables, we introduce class constraints into the type
--   signature of the function.
--   However, this is not possible for (indirectly) recursive arguments.
--
--   A directly recursive argument has the type @T τ₁ … τₙ@, where @τᵢ@ is a
--   type expressions (not necessarily type variables). We assume that @τᵢ'@
--   does not contain @T@ for any @i@, as this would constitute a non-positive
--   occurrence of @T@ and make @T@ invalid in Coq.
--   For these arguments, instead of the function @f@ we call @fT@ recursively.
--
--   An indirectly recursive argument is an argument of a type that is not @T@,
--   but contains @T@.
--   These arguments are problematic because we can neither use @f@ on them
--   (as that would generally require a @C@ instance of @T@) nor can we use
--   @fT@.
--
--   The problem is solved by introducing a local function @fT'@ for every type
--   @T'@ that contains @T@ that inlines the definition of a @T'@ instance of
--   @C@, and call this function for arguments of type @T'@.
--   These local functions are as polymorphic as possible to reduce the number
--   of local functions we need.
--
--   For example, if we want to generate an instance for the Haskell type
--
--   > data Forest a = AForest [Forest a]
--   >               | IntForest [Forest Int]
--   >               | BoolForest [Forest Bool]
--
--   only one local function is needed. In the case of @Normalform@, the local
--   function would look as follows.
--
--   > nf'ListForest_ {a b : Type} `{Normalform Shape Pos a b}
--   >   : List Shape Pos (Forest Shape Pos a)
--   >   -> Free Shape Pos (List Identity.Shape Identity.Pos
--   >                     (Forest Identity.Shape Identity.Pos b))
--
--   To generate these local functions, for every type expression @τ₍ᵢ,ⱼ₎@ in the
--   constructors of @T@, we collect all types that contain the original type
--   @T@.
--   More specifically, a type expression @T' τ₁ … τₙ@ is collected if
--   @τᵢ = T τ₁' … τₙ'@ for some type expressions @τ₁, …, τₙ@, or if @τᵢ@
--   is collected for some @i@.
--   During this process, any type expression that does not contain @T@ is
--   replaced by a placeholder variable @_@.
--
--   We keep track of which types correspond to which function with a map.
--
--   The generated functions @fT₁, …, fTₙ@ for @n@ mutually recursive types
--   @T₁, … Tₙ@ are a set of @n@ @Fixpoint@ definitions linked with @with@.
--   Indirectly recursive types and local functions based on them are computed
--   for each type.
--   In this case, a type @T'@ is considered indirectly recursive if it
--   contains any of the types @T₁, …, Tₙ@.
--   Arguments of type @Tᵢ@ can be treated like directly recursive arguments.
module FreeC.Backend.Coq.Converter.TypeDecl.TypeclassInstances where

import           Control.Monad
  ( foldM, mapAndUnzipM, replicateM )
import           Control.Monad.Extra              ( concatMapM )
import           Data.List                        ( nub )
import qualified Data.List.NonEmpty               as NonEmpty
import qualified Data.Map.Strict                  as Map
import           Data.Maybe                       ( fromJust )
import           Language.Coq.Subst

import qualified FreeC.Backend.Coq.Base           as Coq.Base
import           FreeC.Backend.Coq.Converter.Free
import qualified FreeC.Backend.Coq.Syntax         as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.Fresh
import           FreeC.Environment.LookupOrFail
import           FreeC.IR.SrcSpan                 ( SrcSpan(NoSrcSpan) )
import           FreeC.IR.Subst
import qualified FreeC.IR.Syntax                  as IR
import           FreeC.IR.TypeSynExpansion
import           FreeC.IR.Unification
import           FreeC.Monad.Converter
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Instance Generation                                                       --
-------------------------------------------------------------------------------
-- | Data type for a type with certain components replaced by underscores.
data StrippedType
  = StrippedType
  | StrippedTypeCon IR.TypeConName [StrippedType]
 deriving ( Eq, Ord, Show )

isStripped :: StrippedType -> Bool
isStripped StrippedType = True
isStripped _            = False

-- | Type synonym for a map mapping types to function names.
type TypeMap' = Map.Map IR.Type Coq.Qualid

type TypeMap = Map.Map StrippedType Coq.Qualid

-- | Builds instances for all supported typeclasses.
--   Currently, @Normalform@ and @ShareableArgs@ instances are generated.
generateTypeclassInstances :: [IR.TypeDecl] -> Converter [Coq.Sentence]
generateTypeclassInstances dataDecls = do
  -- The types of the data declaration's constructors' arguments.
  let argTypes = map (concatMap IR.conDeclFields . IR.dataDeclCons) dataDecls
  -- The same types where all type synonyms are expanded.
  argTypesExpanded <- mapM (mapM expandAllTypeSynonyms) argTypes
  -- A list where all fully-applied type constructors that do not contain one of the types
  -- for which we are defining instances and all type variables are replaced with
  -- the same type variable (an underscore). The list is reversed so its entries are
  -- in topological order.
  let reducedTypes = map (nub . reverse . concatMap collectSubTypes)
        argTypesExpanded
  -- Like 'reducedTypes', but with all occurrences of the types for which we are defining
  -- instances and all type variables removed from the list.
  -- This leaves exactly the types with indirect recursion, with all non-recursive
  -- components replaced by underscores.
  let recTypeList = map
        (filter (\t -> not (t `elem` declTypes || isStripped t))) reducedTypes
  -- Construct @Normalform@ instances.
  nfInstances <- buildInstances recTypeList
    (fromJust $ Coq.unpackQualid Coq.Base.nf')
    (fromJust $ Coq.unpackQualid Coq.Base.normalform) nfBindersAndReturnType
    buildNormalformValue
  -- Construct @ShareableArgs@ instances.
  shareableArgsInstances <- buildInstances recTypeList
    (fromJust $ Coq.unpackQualid Coq.Base.shareArgs)
    (fromJust $ Coq.unpackQualid Coq.Base.shareableArgs)
    shareArgsBindersAndReturnType buildShareArgsValue
  return (nfInstances ++ shareableArgsInstances)
 where
  -- | The (mutually recursive) data types for which we are defining
  --   instances, converted to types. All type variable are converted
  --   to underscores.
  declTypes :: [StrippedType]
  declTypes = [StrippedTypeCon (IR.typeDeclQName dataDecl)
                (replicate (length (IR.typeDeclArgs dataDecl)) StrippedType)
              | dataDecl <- dataDecls
              ]

  -- The names of the type constructors of the data types for which
  -- we are defining instances.
  typeConNames :: [IR.TypeConName]
  typeConNames = map IR.typeDeclQName dataDecls

  -- | Constructs instances of a typeclass for a set of mutually recursive
  --   types. The typeclass is specified by the arguments.
  buildInstances
    :: [[StrippedType]]
    -- ^ For each data declaration, this list contains the occurrences of
    -- indirect recursion in the constructors of that data declaration.
    -> String -- ^ The name of the class function.
    -> String -- ^ The name of the typeclass.
    -> (StrippedType
        -> Coq.Qualid
        -> Converter ([Coq.Binder], [Coq.Binder], Coq.Term, Coq.Term))
    -- ^ A function to get class-specific binders and return types.
    -> (TypeMap
        -> Coq.Qualid
        -> [(StrippedType, Coq.Qualid)]
        -> Converter Coq.Term)
    -- ^ A function to compute a class-specific value given a data constructor
    --   with arguments.
    -> Converter [Coq.Sentence]
  buildInstances recTypeList functionPrefix className getBindersAndReturnTypes
    buildValue = do
      -- This map defines the name of the top-level class function for each
      -- of the mutually recursive types.
      -- It must be defined outside of a local environment to prevent any
      -- clashes of the function names with other names.
      topLevelMap <- nameFunctionsAndInsert functionPrefix Map.empty declTypes
      (fixBodies, instances) <- mapAndUnzipM
        (uncurry (buildFixBodyAndInstance topLevelMap))
        (zip declTypes recTypeList)
      return
        $ Coq.comment (className
                       ++ " instance"
                       ++ ['s' | length dataDecls > 1]
                       ++ " for "
                       ++ showPretty (map IR.typeDeclName dataDecls))
        : Coq.FixpointSentence (Coq.Fixpoint (NonEmpty.fromList fixBodies) [])
        : instances
   where
        -- Constructs the class function and class instance for a single type.
    buildFixBodyAndInstance
      :: TypeMap
      -- ^ A map to map occurrences of the top-level types to recursive
      --   function calls.
      -> StrippedType -- ^ The type for which we are defining an instance.
      -> [StrippedType] -- ^ The list of indirectly recursive types.
      -> Converter (Coq.FixBody, Coq.Sentence)
    buildFixBodyAndInstance topLevelMap t recTypes = do
      -- Locally visible definitions are defined in a local environment.
      (fixBody, typeLevelMap, instanceBinders, instanceRetType) <- localEnv $ do
        -- This map names necessary local functions and maps indirectly
        -- recursive types to the appropriate function names.
        typeLevelMap
          <- nameFunctionsAndInsert functionPrefix topLevelMap recTypes
        -- Name the argument of type @t@ given to the class
        -- function.
        topLevelVar <- freshCoqQualid freshArgPrefix
        -- Compute class-specific binders and return types.
        (implicitBinders, explicitBinders, retType, instanceRetType)
          <- getBindersAndReturnTypes t topLevelVar
        -- Build the implementation of the class function.
        let functionBinders = implicitBinders ++ explicitBinders
        fixBody <- makeFixBody typeLevelMap topLevelVar t functionBinders
          retType recTypes
        return (fixBody, typeLevelMap, implicitBinders, instanceRetType)
      -- Build the class instance for the given type.
      -- The instance must be defined outside of a local environment so
      -- that the instance name does not clash with any other names.
      instanceDefinition
        <- buildInstance typeLevelMap t instanceBinders instanceRetType
      return (fixBody, instanceDefinition)

    -- | Builds an instance for a specific type and typeclass.
    buildInstance
      :: TypeMap
      -- ^ A mapping from (in)directly recursive types to function names.
      -> StrippedType -- ^ The type for which we are defining an instance.
      -> [Coq.Binder] -- ^ The binders for the type class instance.
      -> Coq.Term -- ^ The type of the instance.
      -> Converter Coq.Sentence
    buildInstance m t binders retType = do
      -- Define the class function as the function to which the current type
      -- is mapped.
      let instanceBody
            = (Coq.bare functionPrefix, Coq.Qualid (fromJust (Map.lookup t m)))
      instanceName <- nameFunction className t
      return
        $ Coq.InstanceSentence
        (Coq.InstanceDefinition instanceName (freeArgsBinders ++ binders)
         retType [instanceBody] Nothing)

    -- | Generates the implementation of the body of a class function for the
    --   given type.
    makeFixBody
      :: TypeMap
      -- ^ A mapping from (in)directly recursive types to function names.
      -> Coq.Qualid -- ^ The name of the argument of type @t@.
      -> StrippedType -- ^ The type for which we are defining an instance.
      -> [Coq.Binder] -- ^ The binders for the class function.
      -> Coq.Term -- ^ The return type of the class function.
      -> [StrippedType] -- ^ The list of indirectly recursive types.
      -> Converter Coq.FixBody
    makeFixBody m varName t binders retType recTypes = do
      rhs <- generateBody m varName t recTypes
      return
        $ Coq.FixBody (fromJust (Map.lookup t m))
        (NonEmpty.fromList (freeArgsBinders ++ binders))
        (Just (Coq.StructOrder varName)) (Just retType) rhs

    -- | Creates the function body for a class function by creating local
    --   functions for all indirectly recursive types.
    generateBody
      :: TypeMap
      -- ^ A mapping from (in)directly recursive types to function names.
      -> Coq.Qualid -- ^ The name of the argument of type @t@.
      -> StrippedType -- ^ The type for which we are defining an instance.
      -> [StrippedType] -- ^ The list of indirectly recursive types.
      -> Converter Coq.Term

    -- If there are no indirectly recursive types, match on the constructors of
    -- the original type.
    generateBody m varName t []
      = matchConstructors m varName t
    -- For each indirectly recursive type, create a local function as a
    -- @let fix@ declaration and generate the definition of the class function
    -- for that type.
    -- This local declaration is wrapped around all remaining declarations and
    -- is therefore visible when defining them.
    generateBody m varName t (recType : recTypes) = do
      inBody <- generateBody m varName t recTypes
      var <- freshCoqQualid freshArgPrefix
      -- Create the body of the local function by matching on the type's
      -- constructors.
      letBody <- matchConstructors m var recType
      (implicitBinders, explicitBinders, retType, _)
        <- getBindersAndReturnTypes recType var
      let binders            = implicitBinders ++ explicitBinders
          Just localFuncName = Map.lookup recType m
      return
        $ Coq.Let localFuncName [] Nothing
        (Coq.Fix
         (Coq.FixOne (Coq.FixBody localFuncName (NonEmpty.fromList binders)
                      (Just (Coq.StructOrder var)) (Just retType) letBody)))
        inBody

    -- | Matches on the constructors of a type.
    matchConstructors
      :: TypeMap -> Coq.Qualid -> StrippedType -> Converter Coq.Term
    matchConstructors m varName t@(StrippedTypeCon conName _) = do
      entry <- lookupEntryOrFail NoSrcSpan IR.TypeScope conName
      equations <- mapM (buildEquation m t) (entryConsNames entry)
      return $ Coq.match (Coq.Qualid varName) equations
    matchConstructors _ _ StrippedType
      = error "generateTypeclassInstances: unexpected type placeholder."

    -- | Creates a match equation on a given data constructor with a
    --   class-specific right-hand side.
    buildEquation
      :: TypeMap -> StrippedType -> IR.ConName -> Converter Coq.Equation
    buildEquation m t conName = do
      conEntry <- lookupEntryOrFail NoSrcSpan IR.ValueScope conName
      retType <- expandAllTypeSynonyms (entryReturnType conEntry)
      -- Get the Coq name of the constructor.
      let conIdent = entryIdent conEntry
      -- Generate fresh variables for the constructor's parameters.
      conArgIdents <- freshQualids (entryArity conEntry) freshArgPrefix
      -- Replace all underscores with fresh variables before unification.
      tFreshVars <- insertFreshVariables t
      sub <- unifyOrFail NoSrcSpan tFreshVars retType
      -- Find out the type of each constructor argument by unifying its return
      -- type with the given type expression and applying the resulting
      -- substitution to each constructor argument's type.
      -- Then convert all irrelevant components to underscores again so the
      -- type can be looked up in the type map.
      expandedArgTypes <- mapM expandAllTypeSynonyms (entryArgTypes conEntry)
      let modArgTypes = map (stripType . applySubst sub) expandedArgTypes
      let lhs = Coq.ArgsPat conIdent (map Coq.QualidPat conArgIdents)
      -- Build the right-hand side of the equation by applying the
      -- class-specific function @buildValue@.
      rhs <- buildValue m conIdent (zip modArgTypes conArgIdents)
      return $ Coq.equation lhs rhs

  -------------------------------------------------------------------------------
  -- Functions to Produce @Normalform@ Instances                                 --
  -------------------------------------------------------------------------------
  -- | The binders and return types for the @Normalform@ class function and instance.
  nfBindersAndReturnType
    :: StrippedType
    -- ^ The type @t@ for which we are defining an instance.
    -> Coq.Qualid -- ^ The name of the argument of type @t@.
    -> Converter
    ( [Coq.Binder] -- Type variable binders and @Normalform@ constraints.
    , [Coq.Binder] -- Binder for the argument of type @t@.
    , Coq.Term -- Return type of @nf'@.
    , Coq.Term -- Return type of the @Normalform@ instance.
    )
  nfBindersAndReturnType t varName = do
    (sourceType, sourceVars) <- toCoqType t
    -- The return types of the type variables' @Normalform@ instances.
    let nTypes            = map (\v -> genericApply Coq.Base.nType []
                                 [Coq.Qualid v, Coq.Underscore] []) sourceVars
        -- Build a substitution to create the normalized type from the source
        -- type.
        targetTypeMap     = buildNFSubst (zip sourceVars nTypes)
        targetType        = subst targetTypeMap sourceType
        -- For each type variable @aᵢ@, build a constraint
        -- @`{Normalform Shape Pos aᵢ}@.
        constraints       = map Coq.Base.normalformBinder sourceVars
        varBinder         = [typeVarBinder sourceVars | not (null sourceVars)]
        binders           = varBinder ++ constraints
        -- Create an explicit argument binder for the value to be normalized.
        topLevelVarBinder
          = Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit varName sourceType
        instanceRetType   = genericApply Coq.Base.normalform [] [] [sourceType]
        funcRetType       = applyFree targetType
    return (binders, [topLevelVarBinder], funcRetType, instanceRetType)
   where
    buildNFSubst :: [(Coq.Qualid, Coq.Term)] -> Map.Map Coq.Qualid Coq.Term
    buildNFSubst kvs = Map.insert Coq.Base.shape (Coq.Qualid Coq.Base.idShape)
      (Map.insert Coq.Base.pos (Coq.Qualid Coq.Base.idPos)
       (foldr (uncurry Map.insert) Map.empty kvs))

  -- | Builds a normalized @Free@ value for the given constructor
  --   and constructor arguments.
  buildNormalformValue
    :: TypeMap
    -- ^ A map to associate types with the appropriate functions to call.
    -> Coq.Qualid -- ^ The data constructor used to build a value.
    -> [(StrippedType, Coq.Qualid)]
    -- ^ The types and names of the constructor's arguments.
    -> Converter Coq.Term
  buildNormalformValue nameMap consName = buildNormalformValue' []
   where
    -- | Like 'buildNormalformValue', but with an additional parameter to accumulate
    --   bound variables.
    buildNormalformValue'
      :: [Coq.Term] -> [(StrippedType, Coq.Qualid)] -> Converter Coq.Term

    -- If all components have been normalized, apply the constructor to
    -- the normalized components.
    buildNormalformValue' boundVars [] = do
      args <- mapM generatePure (reverse boundVars)
      generatePure (Coq.app (Coq.Qualid consName) args)
    -- For each component, apply the appropriate function, bind the
    -- result and do the remaining computation.
    buildNormalformValue' boundVars ((t, varName) : consVars)
      = let f = (\nx -> buildNormalformValue' (nx : boundVars) consVars)
        in case Map.lookup t nameMap of
             -- For recursive or indirectly recursive calls, the type map
             -- returns the name of the appropriate function to call.
             Just funcName -> do
               -- Because the functions work on bare values, the component
               -- must be bound before applying the normalization.
               generateBind (Coq.Qualid varName) freshArgPrefix Nothing
                 (\x -> generateBind (Coq.app (Coq.Qualid funcName) [x])
                  freshNormalformArgPrefix Nothing f)
             -- If there is no entry in the type map, we can assume that an instance
             -- already exists. Therefore, we apply @nf@ to the component to receive
             -- a normalized value.
             Nothing       -> generateBind
               (Coq.app (Coq.Qualid Coq.Base.nf) [Coq.Qualid varName])
               freshNormalformArgPrefix Nothing f

  -------------------------------------------------------------------------------
  -- Functions to Produce @ShareableArgs@ Instances                              --
  -------------------------------------------------------------------------------
  -- | The binders and return types for the @ShareableArgs@ class function and instance.
  shareArgsBindersAndReturnType
    :: StrippedType
    -- ^ The type @t@ for which we are defining an instance.
    -> Coq.Qualid -- ^ The name of the argument of type @t@.
    -> Converter
    ( [Coq.Binder] -- Binders to add to the type class and functions.
    , [Coq.Binder] -- Binders to add to the function only.
    , Coq.Term -- Return type of @shareArgs@.
    , Coq.Term -- Return type of the @ShareableArgs@ instance.
    )
  shareArgsBindersAndReturnType t varName = do
    (coqType, vars) <- toCoqType t
    let constraints     = map Coq.Base.shareableArgsBinder vars
        typeVarBinders  = [typeVarBinder vars | not (null vars)]
        implicitBinders = typeVarBinders ++ constraints
        varBinder
          = Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit varName coqType
        explicitBinders = [Coq.Base.strategyBinder, varBinder]
        instanceRetType = genericApply Coq.Base.shareableArgs [] [] [coqType]
        funcRetType     = applyFree coqType
    return (implicitBinders, explicitBinders, funcRetType, instanceRetType)

  -- | Shares all arguments of the given constructor and reconstructs the
  --   value with the shared components.
  buildShareArgsValue
    :: TypeMap
    -- ^ A map to associate types with the appropriate functions to call.
    -> Coq.Qualid -- ^ The data constructor used to build a value.
    -> [(StrippedType, Coq.Qualid)]
    -- ^ The types and names of the constructor's arguments.
    -> Converter Coq.Term
  buildShareArgsValue nameMap consName = buildShareArgsValue' []
   where
    buildShareArgsValue'
      :: [Coq.Term] -> [(StrippedType, Coq.Qualid)] -> Converter Coq.Term
    buildShareArgsValue' vals [] = generatePure
      (Coq.app (Coq.Qualid consName) (reverse vals))
    buildShareArgsValue' vals ((t, varName) : consVars) = do
      let funcName = Map.findWithDefault Coq.Base.shareArgs t nameMap
          lhs
            = genericApply Coq.Base.shareWith [Coq.Qualid Coq.Base.strategyArg]
            [] [Coq.Qualid funcName, Coq.Qualid varName]
      generateBind lhs freshSharingArgPrefix Nothing
        (\val -> buildShareArgsValue' (val : vals) consVars)

  -------------------------------------------------------------------------------
  -- Helper Functions                                                          --
  -------------------------------------------------------------------------------
  -- | Creates an entry with a unique name for each of the given types and
  --   inserts them into the given map.
  nameFunctionsAndInsert
    :: String -> TypeMap -> [StrippedType] -> Converter TypeMap
  nameFunctionsAndInsert prefix = foldM (nameFunctionAndInsert prefix)

  -- | Like 'nameFunctionsAndInsert', but for a single type.
  nameFunctionAndInsert
    :: String -> TypeMap -> StrippedType -> Converter TypeMap
  nameFunctionAndInsert prefix m t = do
    name <- nameFunction prefix t
    return (Map.insert t name m)

  -- | Names a function based on a type expression while avoiding name clashes
  --   with other identifiers.
  nameFunction :: String -> StrippedType -> Converter Coq.Qualid
  nameFunction prefix t = do
    prettyType <- showPrettyType t
    freshCoqQualid (prefix ++ prettyType)

  -- | Collects all fully-applied type constructors of arity at least 1
  --   (including their arguments) that occur in the given type. All arguments
  --   that do not contain occurrences of the types for which we are defining
  --   an instance are replaced by the type variable @_@.
  --   The resulting list contains (in reverse topological order) exactly all
  --   types for which we must define a separate function in the instance
  --   definition, where all occurrences of @_@ represent the polymorphic
  --   components of the function.
  collectSubTypes :: IR.Type -> [StrippedType]
  collectSubTypes = collectFullyAppliedTypes True
   where
    -- | Like 'collectSubTypes', but with an additional flag to denote whether
    --   @t@ is a full application of a type constructor, e.g. @Pair Int Bool@,
    --   or a partial application, e.g. @Pair Int@.
    --   Only full applications are collected.
    collectFullyAppliedTypes :: Bool -> IR.Type -> [StrippedType]
    collectFullyAppliedTypes fullApplication t@(IR.TypeApp _ l r)
      -- The left-hand side of a type application is the partial
      -- application of a type constructor.
      -- The right-hand side is a fully-applied type constructor,
      -- a variable or a function type.
       = let remainingTypes = collectFullyAppliedTypes False l
               ++ collectFullyAppliedTypes True r
         in if fullApplication
              then stripType t : remainingTypes
              else remainingTypes
    -- Type variables, function types and type constructors with arity 0 are not
    -- collected.
    collectFullyAppliedTypes _ _ = []

  -- | Returns the same type with all type expressions that do not contain one
  --   of the type constructors for which we are defining instances replaced
  --   with the type variable @_@.
  stripType :: IR.Type -> StrippedType
  stripType = stripType' False
   where
    -- | Like 'stripType', but with an additional flag to denote whether an
    --   occurrence of a relevant type was found in an argument of a type
    --   application.
    --   This is necessary so that, for example, @Pair Bool t@ is not
    --   transformed to @_ t@, but to @Pair _ t@.
    stripType' :: Bool -> IR.Type -> StrippedType
    stripType' flag (IR.TypeCon _ conName)
      | flag || conName `elem` typeConNames = StrippedTypeCon conName []
      | otherwise = StrippedType
    -- For a type application, check if a relevant type occurs in its
    -- right-hand side.
    stripType' flag (IR.TypeApp _ l r) = case stripType' False r of
      -- If not, check if a relevant type occurs in its left-hand side,
      -- otherwise replace the whole expression with an underscore.
      StrippedType -> case stripType' flag l of
        StrippedType             -> StrippedType
        StrippedTypeCon con args -> StrippedTypeCon con (args ++ [StrippedType])
      -- If a relevant type does occur in the right-hand side,
      -- the type application must be preserved, so only its arguments are
      -- stripped.
      r'           -> let StrippedTypeCon con args = stripType' True l
                      in StrippedTypeCon con (args ++ [r'])
    -- Type variables and function types are not relevant and are replaced by @_@.
    stripType' _ _ = StrippedType

  showPrettyType :: StrippedType -> Converter String

  -- For a placeholder, show "_".
  showPrettyType StrippedType               = return "_"
  -- For a type constructor and its arguments, return the constructor's
  -- Coq identifier as a string with the conversions of the arguments appended.
  showPrettyType (StrippedTypeCon con args) = do
    prettyCon <- fromJust . (>>= Coq.unpackQualid)
      <$> inEnv (lookupIdent IR.TypeScope con)
    prettyArgs <- concatMapM showPrettyType args
    return (prettyCon ++ prettyArgs)

  -- | Converts a @StrippedType@ to an @IR.Type@, replacing all
  --   placeholders with fresh variables.
  insertFreshVariables :: StrippedType -> Converter IR.Type
  insertFreshVariables StrippedType               = do
    freshVar <- freshHaskellIdent freshArgPrefix
    return (IR.TypeVar NoSrcSpan freshVar)
  insertFreshVariables (StrippedTypeCon con args) = do
    args' <- mapM insertFreshVariables args
    return (foldl (IR.TypeApp NoSrcSpan) (IR.TypeCon NoSrcSpan con) args')

  -- | Binders for (implicit) Shape and Pos arguments.
  --
  --   > freeArgsBinders = [ {Shape : Type}, {Pos : Shape -> Type} ]
  freeArgsBinders :: [Coq.Binder]
  freeArgsBinders = genericArgDecls Coq.Implicit

  -- | Shortcut for the construction of an implicit binder for type variables.
  --
  --   > typeVarBinder [α₁, …, an] = {α₁ …αₙ : Type}
  typeVarBinder :: [Coq.Qualid] -> Coq.Binder
  typeVarBinder typeVars
    = Coq.typedBinder Coq.Ungeneralizable Coq.Implicit typeVars Coq.sortType

  -- | Given an @A@, returns @Free Shape Pos A@.
  applyFree :: Coq.Term -> Coq.Term
  applyFree a = genericApply Coq.Base.free [] [] [a]

  -- | Converts a type into a Coq type (a term) with fresh Coq
  --   identifiers for all underscores.
  --   Returns a pair of the result term and a list of the fresh variables.
  toCoqType :: StrippedType -- ^ The type to convert.
            -> Converter (Coq.Term, [Coq.Qualid])

  -- A type variable is translated into a fresh type variable.
  toCoqType StrippedType               = do
    x <- freshCoqQualid freshTypeVarPrefix
    return (Coq.Qualid x, [x])
  toCoqType (StrippedTypeCon con args) = do
    entry <- lookupEntryOrFail NoSrcSpan IR.TypeScope con
    (coqArgs, freshVars) <- mapAndUnzipM toCoqType args
    return (genericApply (entryIdent entry) [] [] coqArgs, concat freshVars)

  -- | Produces @n@ new Coq identifiers (Qualids) with the same prefix.
  freshQualids :: Int -> String -> Converter [Coq.Qualid]
  freshQualids n prefix = replicateM n (freshCoqQualid prefix)
