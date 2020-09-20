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
import           Data.List                        ( nub )
import qualified Data.List.NonEmpty               as NonEmpty
import qualified Data.Map.Strict                  as Map
import           Data.Maybe                       ( fromJust )

import qualified FreeC.Backend.Coq.Base           as Coq.Base
import           FreeC.Backend.Coq.Converter.Free
import qualified FreeC.Backend.Coq.Syntax         as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.Fresh
  ( freshArgPrefix, freshCoqQualid, freshHaskellIdent )
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
-- | Type synonym for a map mapping types to function names.
type TypeMap = Map.Map IR.Type Coq.Qualid

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
        (filter (\t -> not (t `elem` declTypes || IR.isTypeVar t))) reducedTypes
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
  declTypes :: [IR.Type]
  declTypes = [IR.typeConApp NoSrcSpan (IR.typeDeclQName dataDecl)
                (replicate (length (IR.typeDeclArgs dataDecl)) placeholderVar)
              | dataDecl <- dataDecls
              ]

  -- The names of the type constructors of the data types for which
  -- we are defining instances.
  typeConNames :: [IR.TypeConName]
  typeConNames = map IR.typeDeclQName dataDecls

  -- | Constructs instances of a typeclass for a set of mutually recursive
  --   types. The typeclass is specified by the arguments.
  buildInstances
    :: [[IR.Type]]
    -- ^ For each data declaration, this list contains the occurrences of
    -- indirect recursion in the constructors of that data declaration.
    -> String -- ^ The name of the class function.
    -> String -- ^ The name of the typeclass.
    -> (IR.Type
        -> Coq.Qualid
        -> Converter ([Coq.Binder], Coq.Binder, Coq.Term, Coq.Term))
    -- ^ A function to get class-specific binders and return types.
    -> (TypeMap -> Coq.Qualid -> [(IR.Type, Coq.Qualid)] -> Converter Coq.Term)
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
      -> IR.Type -- ^ The type for which we are defining an instance.
      -> [IR.Type] -- ^ The list of indirectly recursive types.
      -> Converter (Coq.FixBody, Coq.Sentence)
    buildFixBodyAndInstance topLevelMap t recTypes = do
      -- Locally visible definitions are defined in a local environment.
      (fixBody, typeLevelMap, binders, instanceRetType) <- localEnv $ do
        -- This map names necessary local functions and maps indirectly
        -- recursive types to the appropriate function names.
        typeLevelMap
          <- nameFunctionsAndInsert functionPrefix topLevelMap recTypes
        -- Name the argument of type @t@ given to the class
        -- function.
        topLevelVar <- freshCoqQualid freshArgPrefix
        -- Compute class-specific binders and return types.
        (binders, varBinder, retType, instanceRetType)
          <- getBindersAndReturnTypes t topLevelVar
        -- Build the implementation of the class function.
        fixBody <- makeFixBody typeLevelMap topLevelVar t
          (binders ++ [varBinder]) retType recTypes
        return (fixBody, typeLevelMap, binders, instanceRetType)
      -- Build the class instance for the given type.
      -- The instance must be defined outside of a local environment so
      -- that the instance name does not clash with any other names.
      instanceDefinition <- buildInstance typeLevelMap t binders instanceRetType
      return (fixBody, instanceDefinition)

    -- | Builds an instance for a specific type and typeclass.
    buildInstance
      :: TypeMap
      -- ^ A mapping from (in)directly recursive types to function names.
      -> IR.Type -- ^ The type for which we are defining an instance.
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
      -> IR.Type -- ^ The type for which we are defining an instance.
      -> [Coq.Binder] -- ^ The binders for the class function.
      -> Coq.Term -- ^ The return type of the class function.
      -> [IR.Type] -- ^ The list of indirectly recursive types.
      -> Converter Coq.FixBody
    makeFixBody m varName t binders retType recTypes = do
      rhs <- generateBody m varName t recTypes
      return
        $ Coq.FixBody (fromJust (Map.lookup t m))
        (NonEmpty.fromList (freeArgsBinders ++ binders)) Nothing (Just retType)
        rhs

    -- | Creates the function body for a class function by creating local
    --   functions for all indirectly recursive types.
    generateBody
      :: TypeMap
      -- ^ A mapping from (in)directly recursive types to function names.
      -> Coq.Qualid -- ^ The name of the argument of type @t@.
      -> IR.Type -- ^ The type for which we are defining an instance.
      -> [IR.Type] -- ^ The list of indirectly recursive types.
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
      (binders, varBinder, retType, _) <- getBindersAndReturnTypes recType var
      let Just localFuncName = Map.lookup recType m
      return
        $ Coq.Let localFuncName [] Nothing
        (Coq.Fix (Coq.FixOne (Coq.FixBody localFuncName
                              (NonEmpty.fromList (binders ++ [varBinder]))
                              Nothing (Just retType) letBody))) inBody

    -- | Matches on the constructors of a type.
    matchConstructors :: TypeMap -> Coq.Qualid -> IR.Type -> Converter Coq.Term
    matchConstructors m varName t = do
      let Just conName = IR.getTypeConName t
      entry <- lookupEntryOrFail NoSrcSpan IR.TypeScope conName
      equations <- mapM (buildEquation m t) (entryConsNames entry)
      return $ Coq.match (Coq.Qualid varName) equations

    -- | Creates a match equation on a given data constructor with a
    --   class-specific right-hand side.
    buildEquation :: TypeMap -> IR.Type -> IR.ConName -> Converter Coq.Equation
    buildEquation m t conName = do
      conEntry <- lookupEntryOrFail NoSrcSpan IR.ValueScope conName
      retType <- expandAllTypeSynonyms (entryReturnType conEntry)
      -- Get the Coq name of the constructor.
      let conIdent = entryIdent conEntry
      -- Generate fresh variables for the constructor's parameters.
      conArgIdents <- freshQualids (entryArity conEntry) ("f" ++ freshArgPrefix)
      -- Replace all underscores with fresh variables before unification.
      tFreshVars <- insertFreshVariables t
      subst <- unifyOrFail NoSrcSpan tFreshVars retType
      -- Find out the type of each constructor argument by unifying its return
      -- type with the given type expression and applying the resulting
      -- substitution to each constructor argument's type.
      -- Then convert all irrelevant components to underscores again so the
      -- type can be looked up in the type map.
      expandedArgTypes <- mapM expandAllTypeSynonyms (entryArgTypes conEntry)
      let modArgTypes = map (stripType . applySubst subst) expandedArgTypes
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
    :: IR.Type
    -- ^ The type @t@ for which we are defining an instance.
    -> Coq.Qualid -- ^ The name of the argument of type @t@.
    -> Converter
    ( [Coq.Binder] -- Type variable binders and @Normalform@ constraints.
    , Coq.Binder -- Binder for the argument of type @t@.
    , Coq.Term -- Return type of @nf'@.
    , Coq.Term -- Return type of the @Normalform@ instance.
    )
  nfBindersAndReturnType t varName = do
    -- For each type variable in the type, generate two type variables.
    -- One represents the type's variable itself, the other the result
    -- type of the normalization.
    -- The type is transformed to a Coq type twice, once with @Shape@ and
    -- @Pos@ as arguments for the original type, once with @Identity.Shape@
    -- and @Identity.Pos@ as arguments for the normalized result type.
    (sourceType, sourceVars) <- toCoqType "a" shapeAndPos t
    (targetType, targetVars) <- toCoqType "b" idShapeAndPos t
    -- For each type variable @ai@, build a constraint
    -- @`{Normalform Shape Pos ai bi}@.
    let constraints = zipWith Coq.Base.normalformBinder sourceVars targetVars
    let varBinder
          = [typeVarBinder (sourceVars ++ targetVars) | not (null sourceVars)]
    let binders = varBinder ++ constraints
    -- Create an explicit argument binder for the value to be normalized.
    let topLevelVarBinder
          = Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit varName sourceType
    let instanceRetType = Coq.app (Coq.Qualid Coq.Base.normalform)
          (shapeAndPos ++ [sourceType, targetType])
    let funcRetType = applyFree targetType
    return (binders, topLevelVarBinder, funcRetType, instanceRetType)

  -- | Builds a normalized @Free@ value for the given constructor
  --   and constructor arguments.
  buildNormalformValue
    :: TypeMap
    -- ^ A map to associate types with the appropriate functions to call.
    -> Coq.Qualid -- ^ The data constructor used to build a value.
    -> [(IR.Type, Coq.Qualid)]
    -- ^ The types and names of the constructor's arguments.
    -> Converter Coq.Term
  buildNormalformValue nameMap consName = buildNormalformValue' []
   where
    -- | Like 'buildNormalformValue', but with an additional parameter to accumulate
    --   bound variables.
    buildNormalformValue'
      :: [Coq.Qualid] -> [(IR.Type, Coq.Qualid)] -> Converter Coq.Term

    -- If all components have been normalized, apply the constructor to
    -- the normalized components.
    buildNormalformValue' boundVars [] = do
      args <- mapM (generatePure . Coq.Qualid) (reverse boundVars)
      generatePure (Coq.app (Coq.Qualid consName) args)
    -- For each component, apply the appropriate function, bind the
    -- result and do the remaining computation.
    buildNormalformValue' boundVars ((t, varName) : consVars)
      = case Map.lookup t nameMap of
        -- For recursive or indirectly recursive calls, the type map
        -- returns the name of the appropriate function to call.
        Just funcName -> do
          -- Because the functions work on bare values, the component
          -- must be bound (to a fresh variable).
          x <- freshCoqQualid freshArgPrefix
          -- The result of the normalization will also be bound to a fresh variable.
          nx <- freshCoqQualid ("n" ++ freshArgPrefix)
          -- Do the rest of the computation with the added bound result.
          rhs <- buildNormalformValue' (nx : boundVars) consVars
          -- Construct the actual bindings and return the result.
          let c = Coq.fun [nx] [Nothing] rhs
          let c' = applyBind (Coq.app (Coq.Qualid funcName) [Coq.Qualid x]) c
          return $ applyBind (Coq.Qualid varName) (Coq.fun [x] [Nothing] c')
        -- If there is no entry in the type map, we can assume that an instance
        -- already exists. Therefore, we apply @nf@ to the component to receive
        -- a normalized value.
        Nothing       -> do
          nx <- freshCoqQualid ("n" ++ freshArgPrefix)
          rhs <- buildNormalformValue' (nx : boundVars) consVars
          let c = Coq.fun [nx] [Nothing] rhs
          return
            $ applyBind (Coq.app (Coq.Qualid Coq.Base.nf) [Coq.Qualid varName])
            c

  -------------------------------------------------------------------------------
  -- Functions to Produce @ShareableArgs@ Instances                              --
  -------------------------------------------------------------------------------
  -- | The binders and return types for the @ShareableArgs@ class function and instance.
  shareArgsBindersAndReturnType
    :: IR.Type
    -- ^ The type @t@ for which we are defining an instance.
    -> Coq.Qualid -- ^ The name of the argument of type @t@.
    -> Converter
    ( [Coq.Binder] -- Type variable binders and @ShareableArgs@ constraints.
    , Coq.Binder -- Binder for the argument of type @t@.
    , Coq.Term -- Return type of @shareArgs@.
    , Coq.Term -- Return type of the @ShareableArgs@ instance.
    )
  shareArgsBindersAndReturnType t varName = do
    (coqType, vars) <- toCoqType "a" shapeAndPos t
    let constraints
          = Coq.Base.injectableBinder : map Coq.Base.shareableArgsBinder vars
    let varBinder = [typeVarBinder vars | not (null vars)]
    let binders = varBinder ++ constraints
    let topLevelVarBinder
          = Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit varName coqType
    let instanceRetType = Coq.app (Coq.Qualid Coq.Base.shareableArgs)
          (shapeAndPos ++ [coqType])
    let funcRetType = applyFree coqType
    return (binders, topLevelVarBinder, funcRetType, instanceRetType)

  -- | Shares all arguments of the given constructor and reconstructs the
  --   value with the shared components.
  buildShareArgsValue
    :: TypeMap
    -- ^ A map to associate types with the appropriate functions to call.
    -> Coq.Qualid -- ^ The data constructor used to build a value.
    -> [(IR.Type, Coq.Qualid)]
    -- ^ The types and names of the constructor's arguments.
    -> Converter Coq.Term
  buildShareArgsValue nameMap consName = buildShareArgsValue' []
   where
    buildShareArgsValue'
      :: [Coq.Qualid] -> [(IR.Type, Coq.Qualid)] -> Converter Coq.Term
    buildShareArgsValue' vals [] = generatePure
      (Coq.app (Coq.Qualid consName) (map Coq.Qualid (reverse vals)))
    buildShareArgsValue' vals ((t, varName) : consVars) = do
      sx <- freshCoqQualid ("s" ++ freshArgPrefix)
      rhs <- buildShareArgsValue' (sx : vals) consVars
      case Map.lookup t nameMap of
        Just funcName -> do
          return
            $ applyBind
            (Coq.app (Coq.Qualid Coq.Base.cbneed)
             (shapeAndPos ++ [Coq.Qualid funcName, Coq.Qualid varName]))
            (Coq.fun [sx] [Nothing] rhs)
        Nothing       -> do
          return
            $ applyBind
            (Coq.app (Coq.Qualid Coq.Base.cbneed)
             (shapeAndPos
              ++ [Coq.Qualid Coq.Base.shareArgs, Coq.Qualid varName]))
            (Coq.fun [sx] [Nothing] rhs)

  -------------------------------------------------------------------------------
  -- Helper Functions                                                          --
  -------------------------------------------------------------------------------
  -- | Creates an entry with a unique name for each of the given types and
  --   inserts them into the given map.
  nameFunctionsAndInsert :: String -> TypeMap -> [IR.Type] -> Converter TypeMap
  nameFunctionsAndInsert prefix = foldM (nameFunctionAndInsert prefix)

  -- | Like 'nameFunctionsAndInsert', but for a single type.
  nameFunctionAndInsert :: String -> TypeMap -> IR.Type -> Converter TypeMap
  nameFunctionAndInsert prefix m t = do
    name <- nameFunction prefix t
    return (Map.insert t name m)

  -- | Names a function based on a type expression while avoiding name clashes
  --   with other identifiers.
  nameFunction :: String -> IR.Type -> Converter Coq.Qualid
  nameFunction prefix t = do
    prettyType <- showPrettyType t
    freshCoqQualid (prefix ++ prettyType)

  -- | A type variable that represents irrelevant parts of a type expression.
  --   Represented by an underscore.
  placeholderVar :: IR.Type
  placeholderVar = IR.TypeVar NoSrcSpan "_"

  -- | Collects all fully-applied type constructors of arity at least 1
  --   (including their arguments) that occur in the given type. All arguments
  --   that do not contain occurrences of the types for which we are defining
  --   an instance are replaced by the type variable @_@.
  --   The resulting list contains (in reverse topological order) exactly all
  --   types for which we must define a separate function in the instance
  --   definition, where all occurrences of @_@ represent the polymorphic
  --   components of the function.
  collectSubTypes :: IR.Type -> [IR.Type]
  collectSubTypes = collectFullyAppliedTypes True
   where
    -- | Like 'collectSubTypes', but with an additional flag to denote whether
    --   @t@ is a full application of a type constructor, e.g. @Pair Int Bool@,
    --   or a partial application, e.g. @Pair Int@.
    --   Only full applications are collected.
    collectFullyAppliedTypes :: Bool -> IR.Type -> [IR.Type]
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
  stripType :: IR.Type -> IR.Type
  stripType t = stripType' t False
   where
    -- | Like 'stripType', but with an additional flag to denote whether an
    --   occurrence of a relevant type was found in an argument of a type
    --   application.
    --   This is necessary so that, for example, @Pair Bool t@ is not
    --   transformed to @_ t@, but to @Pair _ t@.
    stripType' :: IR.Type -> Bool -> IR.Type
    stripType' (IR.TypeCon _ conName) flag
      | flag || conName `elem` typeConNames = IR.TypeCon NoSrcSpan conName
      | otherwise = placeholderVar
    -- For a type application, check if a relevant type occurs in its
    -- right-hand side.
    stripType' (IR.TypeApp _ l r) flag = case stripType' r False of
      -- If not, check if a relevant type occurs in its left-hand side,
      -- otherwise replace the whole expression with an underscore.
      r'@(IR.TypeVar _ _) -> case stripType' l flag of
        IR.TypeVar _ _ -> placeholderVar
        l'             -> IR.TypeApp NoSrcSpan l' r'
      -- If a relevant type does occur in the right-hand side,
      -- the type application must be preserved, so only its arguments are
      -- stripped.
      r'                  -> IR.TypeApp NoSrcSpan (stripType' l True) r'
    -- Type variables and function types are not relevant and are replaced by @_@.
    stripType' _ _ = placeholderVar

  -- | Like @showPretty@, but uses the Coq identifiers of the type and its components.
  showPrettyType :: IR.Type -> Converter String

  -- For a type variable, show its name.
  showPrettyType (IR.TypeVar _ varName) = return (showPretty varName)
  -- For a type constructor, return its Coq identifier as a string.
  showPrettyType (IR.TypeCon _ conName) = fromJust . (>>= Coq.unpackQualid)
    <$> inEnv (lookupIdent IR.TypeScope conName)
  -- For a type application, convert both sides and concatenate them.
  showPrettyType (IR.TypeApp _ l r)     = do
    lPretty <- showPrettyType l
    rPretty <- showPrettyType r
    return (lPretty ++ rPretty)
  -- Function types should have been converted into variables.
  showPrettyType (IR.FuncType _ _ _)
    = error "Function types should have been eliminated."

  -- | Replaces all variables in a type with fresh variables.
  insertFreshVariables :: IR.Type -> Converter IR.Type
  insertFreshVariables (IR.TypeVar srcSpan _) = do
    freshVar <- freshHaskellIdent freshArgPrefix
    return (IR.TypeVar srcSpan freshVar)
  insertFreshVariables (IR.TypeApp srcSpan l r) = do
    lFresh <- insertFreshVariables l
    rFresh <- insertFreshVariables r
    return (IR.TypeApp srcSpan lFresh rFresh)
  -- Type constructors and function types are returned as-is.
  insertFreshVariables t = return t

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

  -- | Shortcut for the application of @>>=@.
  applyBind :: Coq.Term -> Coq.Term -> Coq.Term
  applyBind mx f = Coq.app (Coq.Qualid Coq.Base.freeBind) [mx, f]

  -- | Given an @A@, returns @Free Shape Pos A@.
  applyFree :: Coq.Term -> Coq.Term
  applyFree a = genericApply Coq.Base.free [] [] [a]

  -- | @Shape@ and @Pos@ arguments as Coq terms.
  shapeAndPos :: [Coq.Term]
  shapeAndPos = [Coq.Qualid Coq.Base.shape, Coq.Qualid Coq.Base.pos]

  -- | The shape and position function arguments for the identity monad
  --   as a Coq term.
  idShapeAndPos :: [Coq.Term]
  idShapeAndPos = map Coq.Qualid
    [ Coq.Qualified (Coq.ident "Identity") Coq.Base.shapeIdent
    , Coq.Qualified (Coq.ident "Identity") Coq.Base.posIdent
    ]

  -- | Converts a type into a Coq type (a term) with the specified
  --   additional arguments (for example @Shape@ and @Pos@) and fresh Coq
  --   identifiers for all underscores.
  --   Returns a pair of the result term and a list of the fresh variables.
  toCoqType
    :: String -- ^ The prefix of the fresh variables.
    -> [Coq.Term] -- ^ A list of additional arguments, e.g. Shape and Pos.
    -> IR.Type -- ^ The type to convert.
    -> Converter (Coq.Term, [Coq.Qualid])

  -- A type variable is translated into a fresh type variable.
  toCoqType varPrefix _ (IR.TypeVar _ _)           = do
    x <- freshCoqQualid varPrefix
    return (Coq.Qualid x, [x])
  -- A type constructor is applied to the given arguments.
  toCoqType _ extraArgs (IR.TypeCon _ conName)     = do
    entry <- lookupEntryOrFail NoSrcSpan IR.TypeScope conName
    return (Coq.app (Coq.Qualid (entryIdent entry)) extraArgs, [])
  -- For a type application, both arguments are translated recursively
  -- and the collected variables are combined.
  toCoqType varPrefix extraArgs (IR.TypeApp _ l r) = do
    (l', varsl) <- toCoqType varPrefix extraArgs l
    (r', varsr) <- toCoqType varPrefix extraArgs r
    return (Coq.app l' [r'], varsl ++ varsr)
  -- Function types were removed by 'stripType'.
  toCoqType _ _ (IR.FuncType _ _ _)
    = error "Function types should have been eliminated."

  -- | Produces @n@ new Coq identifiers (Qualids) with the same prefix.
  freshQualids :: Int -> String -> Converter [Coq.Qualid]
  freshQualids n prefix = replicateM n (freshCoqQualid prefix)
