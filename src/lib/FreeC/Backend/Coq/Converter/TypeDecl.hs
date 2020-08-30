-- | This module contains functions for converting type synonym and data type
--   declarations and their constructors.
module FreeC.Backend.Coq.Converter.TypeDecl where

import           Control.Monad
  ( foldM, mapAndUnzipM, replicateM, zipWithM )
import           Control.Monad.Extra              ( concatMapM )
import           Data.List                        ( nub, partition )
import qualified Data.List.NonEmpty               as NonEmpty
import           Data.Maybe                       ( catMaybes, fromJust )
import qualified Data.Set                         as Set

import qualified FreeC.Backend.Coq.Base           as Coq.Base
import           FreeC.Backend.Coq.Converter.Arg
import           FreeC.Backend.Coq.Converter.Free
import           FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Syntax         as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.Fresh
import           FreeC.Environment.LookupOrFail
import           FreeC.IR.DependencyGraph
import           FreeC.IR.SrcSpan                 ( SrcSpan(NoSrcSpan) )
import           FreeC.IR.Subst
import qualified FreeC.IR.Syntax                  as IR
import           FreeC.IR.TypeSynExpansion
import           FreeC.IR.Unification
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Strongly Connected Components                                             --
-------------------------------------------------------------------------------
-- | Converts a strongly connected component of the type dependency graph.
convertTypeComponent
  :: DependencyComponent IR.TypeDecl -> Converter [Coq.Sentence]
convertTypeComponent (NonRecursive decl)
  | isTypeSynDecl decl = convertTypeSynDecl decl
  | otherwise = convertDataDecls [decl]
convertTypeComponent (Recursive decls)   = do
  let (typeSynDecls, dataDecls) = partition isTypeSynDecl decls
      typeSynDeclQNames         = Set.fromList
        (map IR.typeDeclQName typeSynDecls)
  sortedTypeSynDecls <- sortTypeSynDecls typeSynDecls
  expandedDataDecls <- mapM
    (expandAllTypeSynonymsInDeclWhere (`Set.member` typeSynDeclQNames))
    dataDecls
  dataDecls' <- convertDataDecls expandedDataDecls
  typeSynDecls' <- concatMapM convertTypeSynDecl sortedTypeSynDecls
  return (dataDecls' ++ typeSynDecls')

-- | Sorts type synonym declarations topologically.
--
--   After filtering type synonym declarations from the a strongly connected
--   component, they are not mutually dependent on each other anymore (expect
--   if they form a cycle). However, type synonyms may still depend on other
--   type synonyms from the same strongly connected component. Therefore we
--   have to sort the declarations in reverse topological order.
sortTypeSynDecls :: [IR.TypeDecl] -> Converter [IR.TypeDecl]
sortTypeSynDecls = mapM fromNonRecursive . groupTypeDecls

-- | Extracts the single type synonym declaration from a strongly connected
--   component of the type dependency graph.
--
--   Reports a fatal error if the component contains mutually recursive
--   declarations (i.e. type synonyms form a cycle).
fromNonRecursive :: DependencyComponent IR.TypeDecl -> Converter IR.TypeDecl
fromNonRecursive (NonRecursive decl) = return decl
fromNonRecursive (Recursive decls)   = reportFatal
  $ Message (IR.typeDeclSrcSpan (head decls)) Error
  $ "Type synonym declarations form a cycle: "
  ++ showPretty (map IR.typeDeclIdent decls)

-------------------------------------------------------------------------------
-- Type Synonym Declarations                                                 --
-------------------------------------------------------------------------------
-- | Tests whether the given declaration is a type synonym declaration.
isTypeSynDecl :: IR.TypeDecl -> Bool
isTypeSynDecl (IR.TypeSynDecl _ _ _ _) = True
isTypeSynDecl (IR.DataDecl _ _ _ _)    = False

-- | Converts a Haskell type synonym declaration to Coq.
convertTypeSynDecl :: IR.TypeDecl -> Converter [Coq.Sentence]
convertTypeSynDecl decl@(IR.TypeSynDecl _ _ typeVarDecls typeExpr)
  = localEnv $ do
    let name = IR.typeDeclQName decl
    Just qualid <- inEnv $ lookupIdent IR.TypeScope name
    typeVarDecls' <- convertTypeVarDecls Coq.Explicit typeVarDecls
    typeExpr' <- convertType' typeExpr
    return [ Coq.definitionSentence qualid
               (genericArgDecls Coq.Explicit ++ typeVarDecls')
               (Just Coq.sortType) typeExpr'
           ]
-- Data type declarations are not allowed in this function.
convertTypeSynDecl (IR.DataDecl _ _ _ _)
  = error "convertTypeSynDecl: Data type declaration not allowed."

-------------------------------------------------------------------------------
-- Data type declarations                                                    --
-------------------------------------------------------------------------------
-- | Converts multiple (mutually recursive) Haskell data type declaration
--   declarations.
--
--   Before the declarations are actually translated, their identifiers are
--   inserted into the current environment. Otherwise the data types would
--   not be able to depend on each other. The identifiers for the constructors
--   are inserted into the current environment as well. This makes the
--   constructors more likely to keep their original name if there is a type
--   variable with the same (lowercase) name.
--
--   After the @Inductive@ sentences for the data type declarations there
--   is one @Arguments@ sentence and one smart constructor declaration for
--   each constructor declaration of the given data types.
convertDataDecls :: [IR.TypeDecl] -> Converter [Coq.Sentence]
convertDataDecls dataDecls = do
  (indBodies, extraSentences) <- mapAndUnzipM convertDataDecl dataDecls
  --instances <- generateInstances dataDecls
  instances <- generateAllInstances dataDecls
  return
    (Coq.comment ("Data type declarations for "
                  ++ showPretty (map IR.typeDeclName dataDecls))
     : Coq.InductiveSentence (Coq.Inductive (NonEmpty.fromList indBodies) [])
     : concat extraSentences ++ instances)

-- | Converts a Haskell data type declaration to the body of a Coq @Inductive@
--   sentence, the @Arguments@ sentences for it's constructors and the smart
--   constructor declarations.
--
--   Type variables declared by the data type or the smart constructors are
--   not visible outside of this function.
convertDataDecl :: IR.TypeDecl -> Converter (Coq.IndBody, [Coq.Sentence])
convertDataDecl (IR.DataDecl _ (IR.DeclIdent _ name) typeVarDecls conDecls) = do
  (body, argumentsSentences) <- generateBodyAndArguments
  smartConDecls <- mapM generateSmartConDecl conDecls
  return
    ( body
    , Coq.comment ("Arguments sentences for " ++ showPretty (IR.toUnQual name))
        : argumentsSentences
        ++ Coq.comment
        ("Smart constructors for " ++ showPretty (IR.toUnQual name))
        : smartConDecls
    )
 where
  -- | Generates the body of the @Inductive@ sentence and the @Arguments@
  --   sentences for the constructors but not the smart constructors
  --   of the data type.
  --
  --   Type variables declared by the data type declaration are visible to the
  --   constructor declarations and @Arguments@ sentences created by this
  --   function, but not outside this function. This allows the smart
  --   constructors to reuse the identifiers for their type arguments (see
  --   'generateSmartConDecl').
  generateBodyAndArguments :: Converter (Coq.IndBody, [Coq.Sentence])
  generateBodyAndArguments = localEnv $ do
    Just qualid <- inEnv $ lookupIdent IR.TypeScope name
    typeVarDecls' <- convertTypeVarDecls Coq.Explicit typeVarDecls
    conDecls' <- mapM convertConDecl conDecls
    argumentsSentences <- mapM generateArgumentsSentence conDecls
    return ( Coq.IndBody qualid (genericArgDecls Coq.Explicit ++ typeVarDecls')
               Coq.sortType conDecls'
           , argumentsSentences
           )

  -- | Converts a constructor of the data type.
  convertConDecl
    :: IR.ConDecl -> Converter (Coq.Qualid, [Coq.Binder], Maybe Coq.Term)
  convertConDecl (IR.ConDecl _ (IR.DeclIdent _ conName) args) = do
    Just conQualid <- inEnv $ lookupIdent IR.ValueScope conName
    Just returnType <- inEnv $ lookupReturnType IR.ValueScope conName
    args' <- mapM convertType args
    returnType' <- convertType' returnType
    return (conQualid, [], Just (args' `Coq.arrows` returnType'))

  -- | Generates the @Arguments@ sentence for the given constructor
  --   declaration.
  generateArgumentsSentence :: IR.ConDecl -> Converter Coq.Sentence
  generateArgumentsSentence (IR.ConDecl _ (IR.DeclIdent _ conName) _) = do
    Just qualid <- inEnv $ lookupIdent IR.ValueScope conName
    let typeVarNames = map IR.typeVarDeclQName typeVarDecls
    typeVarQualids <- mapM (inEnv . lookupIdent IR.TypeScope) typeVarNames
    return (Coq.ArgumentsSentence
            (Coq.Arguments Nothing qualid
             [Coq.ArgumentSpec Coq.ArgMaximal (Coq.Ident typeVarQualid) Nothing
             | typeVarQualid
             <- map fst Coq.Base.freeArgs ++ catMaybes typeVarQualids
             ]))

  -- | Generates the smart constructor declaration for the given constructor
  --   declaration.
  generateSmartConDecl :: IR.ConDecl -> Converter Coq.Sentence
  generateSmartConDecl (IR.ConDecl _ declIdent argTypes) = localEnv $ do
    let conName = IR.declIdentName declIdent
    Just qualid <- inEnv $ lookupIdent IR.ValueScope conName
    Just smartQualid <- inEnv $ lookupSmartIdent conName
    Just returnType <- inEnv $ lookupReturnType IR.ValueScope conName
    typeVarDecls' <- convertTypeVarDecls Coq.Implicit typeVarDecls
    (argIdents', argDecls') <- mapAndUnzipM convertAnonymousArg
      (map Just argTypes)
    returnType' <- convertType returnType
    rhs <- generatePure
      (Coq.app (Coq.Qualid qualid) (map Coq.Qualid argIdents'))
    return (Coq.definitionSentence smartQualid
            (genericArgDecls Coq.Explicit ++ typeVarDecls' ++ argDecls')
            (Just returnType') rhs)
-- Type synonyms are not allowed in this function.
convertDataDecl (IR.TypeSynDecl _ _ _ _)
  = error "convertDataDecl: Type synonym not allowed."

------ Instance generation -------
-- builds instances for all available typeclasses (currently Normalform)
generateAllInstances :: [IR.TypeDecl] -> Converter [Coq.Sentence]
generateAllInstances dataDecls = do
  let argTypes = map (concatMap IR.conDeclFields . IR.dataDeclCons) dataDecls -- :: [[IR.Type]]
  argTypesExpanded
    <- mapM (mapM expandAllTypeSynonyms) argTypes -- :: [[IR.Type]]
  let types = map (nub . reverse . concatMap collectSubTypes) argTypesExpanded
  let recTypeList = map
        (filter (\t -> not (t `elem` declTypes || IR.isTypeVar t))) types
  buildInstances recTypeList "nf'" "Normalform" nfBindersAndReturnType
    buildNormalformValue
 where
  declTypes = map dataDeclToType dataDecls

  conNames = map IR.typeDeclQName dataDecls

  -- makes instances for a specific typeclass
  buildInstances
    :: [[IR.Type]] -- for each dataDecl, the types contained in it with nested occurrences of one of the dataDecls
    -> String -- function prefix, i.e. what functions will be called (e.g. nf' or shareArgs)
    -> String -- name of the typeclass
    -> (IR.Type
        -> Coq.Qualid
        -> Converter ([Coq.Binder], Coq.Binder, Coq.Term, Coq.Term)) -- function to get class-specific binders and return types
    -> (TypeMap
        -> Coq.Qualid
        -> [(IR.Type, Coq.Qualid)]
        -> Converter Coq.Term) -- how to actually build a value
    -> Converter [Coq.Sentence]
  buildInstances recTypeList functionPrefix className getBindersAndReturnTypes
    buildValue = do
      -- The names of the top-level functions must be defined outside of a local
      -- environment to prevent any clashes with other names.
      topLevelMap
        <- nameFunctionsAndInsert functionPrefix emptyTypeMap declTypes
      -- top-level variables, one for each dataDecl
      (typeLevelMaps, topLevelBindersAndReturnTypes, functionDefinitions)
        <- localEnv $ do
          typeLevelMaps <- mapM
            (nameFunctionsAndInsert functionPrefix topLevelMap) recTypeList
          topLevelVars <- freshQualids (length declTypes) "x"
          topLevelBindersAndReturnTypes
            <- zipWithM getBindersAndReturnTypes declTypes topLevelVars
          funcDefs <- buildFunctions topLevelVars typeLevelMaps
            topLevelBindersAndReturnTypes
          return (typeLevelMaps, topLevelBindersAndReturnTypes, funcDefs)
      -- The instance must also be defined outside of a local environment so
      -- that the instance name does not clash with any other names.
      instanceDefinitions <- zipWithM (uncurry buildInstance)
        (zip typeLevelMaps declTypes) topLevelBindersAndReturnTypes
      return (functionDefinitions : instanceDefinitions)
   where
    buildInstance :: TypeMap
                  -> IR.Type
                  -> ([Coq.Binder], Coq.Binder, Coq.Term, Coq.Term)
                  -> Converter Coq.Sentence
    buildInstance m t (binders, _, _, retType) = do
      -- @nf' := nf'T@
      let instanceBody
            = (Coq.bare functionPrefix, Coq.Qualid (fromJust (lookupType t m)))
      instanceName <- Coq.bare <$> nameFunction className t
      return
        $ Coq.InstanceSentence (Coq.InstanceDefinition instanceName binders
                                retType [instanceBody] Nothing)

    buildFunctions :: [Coq.Qualid]
                   -> [TypeMap]
                   -> [([Coq.Binder], Coq.Binder, Coq.Term, Coq.Term)]
                   -> Converter Coq.Sentence
    buildFunctions topLevelVars typeLevelMaps topLevelBindersAndReturnTypes = do
      fixBodies <- zipWithM
        (uncurry (uncurry (uncurry makeFixBody))) -- TODO Refactor more?
        (zip (zip (zip typeLevelMaps topLevelVars) declTypes)
         topLevelBindersAndReturnTypes) recTypeList
      return
        $ Coq.FixpointSentence (Coq.Fixpoint (NonEmpty.fromList fixBodies) [])

    makeFixBody :: TypeMap
                -> Coq.Qualid
                -> IR.Type
                -> ([Coq.Binder], Coq.Binder, Coq.Term, Coq.Term)
                -> [IR.Type]
                -> Converter Coq.FixBody
    makeFixBody m varName t (binders, varBinder, retType, _) recTypes = do
      rhs <- generateBody m varName t recTypes
      return
        $ Coq.FixBody (fromJust (lookupType t m))
        (NonEmpty.fromList (binders ++ [varBinder])) Nothing (Just retType) rhs

    generateBody
      :: TypeMap -> Coq.Qualid -> IR.Type -> [IR.Type] -> Converter Coq.Term
    generateBody m varName t []
      = matchConstructors m varName t
    generateBody m varName t (recType : recTypes) = do
      inBody <- generateBody m varName t recTypes
      var <- Coq.bare <$> freshCoqIdent "x"
      letBody <- matchConstructors m var recType
      (binders, varBinder, retType, _) <- getBindersAndReturnTypes recType var
      let Just localFuncName = lookupType recType m
      return
        $ Coq.Let localFuncName [] Nothing
        (Coq.Fix (Coq.FixOne (Coq.FixBody localFuncName
                              (NonEmpty.fromList (binders ++ [varBinder]))
                              Nothing (Just retType) letBody))) inBody

    matchConstructors :: TypeMap -> Coq.Qualid -> IR.Type -> Converter Coq.Term
    matchConstructors m varName t = do
      let Just conName = IR.getTypeConName t
      entry <- lookupEntryOrFail NoSrcSpan IR.TypeScope conName
      equations <- mapM (buildEquation m t) (entryConsNames entry)
      return $ Coq.match (Coq.Qualid varName) equations

     -- type: type expression for unification
     -- conName : data constructor name of type
    buildEquation
      :: TypeMap
      -> IR.Type
      -> IR.ConName
      -> Converter Coq.Equation -- TODO: rename type args before unification

    buildEquation m t conName = do
      conEntry <- lookupEntryOrFail NoSrcSpan IR.ValueScope conName
      let retType = entryReturnType conEntry
      let conIdent = entryIdent conEntry -- :: Qualid
      conArgIdents <- freshQualids (entryArity conEntry) "fx"
      -- Replace all underscores with fresh variables before unification.
      tFreshVars <- insertFreshVariables t
      subst <- unifyOrFail NoSrcSpan tFreshVars retType
      let modArgTypes = map (stripType . applySubst subst)
            (entryArgTypes conEntry)
      let lhs = Coq.ArgsPat conIdent (map Coq.QualidPat conArgIdents)
      rhs <- buildValue m conIdent (zip modArgTypes conArgIdents)
      return $ Coq.equation lhs rhs

  ------- Type analysis -------
  -- This function collects all fully-applied type constructors 
  -- of arity at least 1 (including their arguments) that occur in the given type.
  -- All arguments that do not contain occurrences of the types for which
  -- we are defining an instance are replaced by the type variable "_".
  -- The resulting list contains (in reverse topological order) exactly all 
  -- types for which we must define a separate function in the instance 
  -- definition, where all occurrences of "_" represent the polymorphic 
  -- components of the function.
  collectSubTypes :: IR.Type -> [IR.Type]
  collectSubTypes = collectFullyAppliedTypes True

  collectFullyAppliedTypes :: Bool -> IR.Type -> [IR.Type]
  collectFullyAppliedTypes fullApplication t@(IR.TypeApp _ l r)
    | fullApplication = stripType t
      : collectFullyAppliedTypes False l ++ collectFullyAppliedTypes True r
    | otherwise
      = collectFullyAppliedTypes False l ++ collectFullyAppliedTypes True r
  -- Type variables, function types and type constructors with arity 0 are not
  -- collected.
  collectFullyAppliedTypes _ _ = []

  -- returns the same type with all 'don't care' types replaced by the variable "_"
  stripType :: IR.Type -> IR.Type
  stripType t = stripType' t False

  stripType' :: IR.Type -> Bool -> IR.Type
  stripType' (IR.TypeCon _ conName) flag
    | flag || conName `elem` conNames = IR.TypeCon NoSrcSpan conName
    | otherwise = IR.TypeVar NoSrcSpan "_"
  stripType' (IR.TypeApp _ l r) flag = case stripType' r False of
    r'@(IR.TypeVar _ _) -> case stripType' l flag of
      (IR.TypeVar _ _) -> IR.TypeVar NoSrcSpan "_" -- makes sure that Don't cares are squashed.
      l'               -> IR.TypeApp NoSrcSpan l' r'
    r'                  -> IR.TypeApp NoSrcSpan (stripType' l True) r'
  -- Type variables and function types are not relevant and are replaced by "_".
  stripType' _ _ = IR.TypeVar NoSrcSpan "_"

----------- Functions specific to a typeclass ------------
------- Functions for building Normalform instances -------
-- regular binders, top-level variable binder, return type of function belonging to type, class name
nfBindersAndReturnType
  :: IR.Type
  -> Coq.Qualid
  -> Converter ([Coq.Binder], Coq.Binder, Coq.Term, Coq.Term)
nfBindersAndReturnType t varName = do
  (sourceType, sourceVars) <- toCoqType "a" shapeAndPos t
  (targetType, targetVars) <- toCoqType "b" idShapeAndPos t
  let constraints = map (buildConstraint "Normalform")
        (zipWith (\v1 v2 -> [v1, v2]) sourceVars targetVars)
  let varBinders
        = [typeBinder (sourceVars ++ targetVars) | not (null sourceVars)]
  let binders = freeArgsBinders ++ varBinders ++ constraints
  let topLevelVarBinder = Coq.typedBinder' Coq.Explicit varName sourceType
  let instanceRetType = Coq.app (Coq.Qualid (Coq.bare "Normalform"))
        (shapeAndPos ++ [sourceType, targetType])
  let funcRetType = applyFree targetType
  return (binders, topLevelVarBinder, funcRetType, instanceRetType)

buildNormalformValue
  :: TypeMap -> Coq.Qualid -> [(IR.Type, Coq.Qualid)] -> Converter Coq.Term
buildNormalformValue nameMap consName = buildNormalformValue' []
 where
  buildNormalformValue'
    :: [Coq.Qualid] -> [(IR.Type, Coq.Qualid)] -> Converter Coq.Term
  buildNormalformValue' vals [] = do
    args <- mapM (generatePure . Coq.Qualid) (reverse vals)
    generatePure (Coq.app (Coq.Qualid consName) args)
  buildNormalformValue' vals ((t, varName) : consVars)
    = case lookupType t nameMap of
      Just funcName -> do
        x <- Coq.bare <$> freshCoqIdent "x"
        nx <- Coq.bare <$> freshCoqIdent "nx"
        rhs <- buildNormalformValue' (nx : vals) consVars
        let c = Coq.fun [nx] [Nothing] rhs
        let c'' = applyBind (Coq.app (Coq.Qualid funcName) [Coq.Qualid x]) c
        return $ applyBind (Coq.Qualid varName) (Coq.fun [x] [Nothing] c'')
      Nothing       -> do
        nx <- Coq.bare <$> freshCoqIdent "nx"
        rhs <- buildNormalformValue' (nx : vals) consVars
        let cont = Coq.fun [nx] [Nothing] rhs
        return
          $ applyBind
          (Coq.app (Coq.Qualid (Coq.bare "nf")) [Coq.Qualid varName]) cont

---------------- Helper functions for types -----------------
-- Like showPretty, but uses the Coq identifiers of the type and its components.
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

-- Converts a data declaration to a type by applying its constructor to the 
-- correct number of variables, denoted by underscores.
dataDeclToType :: IR.TypeDecl -> IR.Type
dataDeclToType dataDecl = IR.typeConApp NoSrcSpan (IR.typeDeclQName dataDecl)
  (replicate (length (IR.typeDeclArgs dataDecl)) (IR.TypeVar NoSrcSpan "_"))

-- Replaces all variables ("don't care" values) with
-- fresh variables.
insertFreshVariables :: IR.Type -> Converter IR.Type
insertFreshVariables (IR.TypeVar srcSpan _) = do
  freshVar <- freshHaskellIdent freshArgPrefix
  return (IR.TypeVar srcSpan freshVar)
insertFreshVariables (IR.TypeApp srcSpan l r) = do
  lFresh <- insertFreshVariables l
  rFresh <- insertFreshVariables r
  return (IR.TypeApp srcSpan lFresh rFresh)
-- Type constructors are returned as-is.
-- Function types should not occur, but are also simply returned.
insertFreshVariables t = return t

------------------- Coq AST helper functions/shortcuts -------------------
-- Binders for (implicit) Shape and Pos arguments.
-- freeArgsBinders = [ {Shape : Type}, {Pos : Shape -> Type} ]
freeArgsBinders :: [Coq.Binder]
freeArgsBinders = map (uncurry (Coq.typedBinder' Coq.Implicit))
  Coq.Base.freeArgs

-- Shortcut for the construction of an implicit binder for type variables.
-- typeBinder [a1, ..., an] = {a1 ... an : Type}
typeBinder :: [Coq.Qualid] -> Coq.Binder
typeBinder typeVars = Coq.typedBinder Coq.Implicit typeVars Coq.sortType

-- Shortcut for the application of >>=.
applyBind :: Coq.Term -> Coq.Term -> Coq.Term
applyBind mx f = Coq.app (Coq.Qualid Coq.Base.freeBind) [mx, f]

-- Given an A, returns Free Shape Pos A
applyFree :: Coq.Term -> Coq.Term
applyFree a = Coq.app (Coq.Qualid Coq.Base.free) (shapeAndPos ++ [a])

-- [Shape, Pos]
shapeAndPos :: [Coq.Term]
shapeAndPos = map Coq.Qualid Coq.Base.shapeAndPos

-- [Identity.Shape, Identity.Pos]
idShapeAndPos :: [Coq.Term]
idShapeAndPos = map Coq.Qualid Coq.Base.idShapeAndPos

-- Constructs an implicit generalized binder (~ type class constraint).
-- buildConstraint name [a1 ... an] = `{name Shape Pos a1 ... an}.
buildConstraint :: String -> [Coq.Qualid] -> Coq.Binder
buildConstraint ident args = Coq.Generalized Coq.Implicit
  (Coq.app (Coq.Qualid (Coq.bare ident)) (shapeAndPos ++ map Coq.Qualid args))

-- converts our type into a Coq type (a term) with new variables for all don't care values.
-- We can also choose the prefix for those variables.
toCoqType
  :: String -> [Coq.Term] -> IR.Type -> Converter (Coq.Term, [Coq.Qualid])
toCoqType varPrefix _ (IR.TypeVar _ _)           = do
  x <- Coq.bare <$> freshCoqIdent varPrefix
  return (Coq.Qualid x, [x])
toCoqType _ extraArgs (IR.TypeCon _ conName)     = do
  entry <- lookupEntryOrFail NoSrcSpan IR.TypeScope conName
  return (Coq.app (Coq.Qualid (entryIdent entry)) extraArgs, [])
toCoqType varPrefix extraArgs (IR.TypeApp _ l r) = do
  (l', varsl) <- toCoqType varPrefix extraArgs l
  (r', varsr) <- toCoqType varPrefix extraArgs r
  return (Coq.app l' [r'], varsl ++ varsr)
toCoqType _ _ (IR.FuncType _ _ _)
  = error "Function types should have been eliminated."

-------------------------------
-- Function name map 
-- For each type that contains one of the types we are defining
-- an instance for - directly or indirectly -, we insert an 
-- entry into a map that returns the name of the function we
-- should call on a value of that type.
-- For all types that do not have a corresponding entry, we 
-- can assume that an instance already exists.
type TypeMap = IR.Type -> Maybe Coq.Qualid

emptyTypeMap :: TypeMap
emptyTypeMap = const Nothing

lookupType :: IR.Type -> TypeMap -> Maybe Coq.Qualid
lookupType = flip ($)

insertType :: IR.Type -> Coq.Qualid -> TypeMap -> TypeMap
insertType k v m t = if k == t then Just v else m t

-- Creates an entry with a unique name for each of the given types and 
-- inserts them into the given map. 
nameFunctionsAndInsert :: String -> TypeMap -> [IR.Type] -> Converter TypeMap
nameFunctionsAndInsert prefix = foldM (nameFunctionAndInsert prefix)

-- Like `nameFunctionsAndInsert`, but for a single type.
nameFunctionAndInsert :: String -> TypeMap -> IR.Type -> Converter TypeMap
nameFunctionAndInsert prefix m t = do
  name <- nameFunction prefix t
  return (insertType t (Coq.bare name) m)

-- Names a function based on a type while avoiding name clashes with other
-- identifiers.
nameFunction :: String -> IR.Type -> Converter String
nameFunction prefix t = do
  prettyType <- showPrettyType t
  freshCoqIdent (prefix ++ prettyType)

-- Produces n new Coq identifiers (Qualids)
freshQualids :: Int -> String -> Converter [Coq.Qualid]
freshQualids n prefix = replicateM n (Coq.bare <$> freshCoqIdent prefix)
