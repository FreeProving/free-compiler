-- | This module contains functions for converting type synonym and data type
--   declarations and their constructors.
module FreeC.Backend.Coq.Converter.TypeDecl
  ( -- * Strongly Connected Components
    convertTypeComponent
  , sortTypeSynDecls
  , fromNonRecursive
    -- * Type Synonym Declarations
  , isTypeSynDecl
  , convertTypeSynDecl
    -- * Data Type Declarations
  , convertDataDecls
  , convertDataDecl
  ) where

import           Control.Monad
  ( foldM, mapAndUnzipM, replicateM )
import           Control.Monad.Extra              ( concatMapM )
import           Data.List                        ( nub, partition )
import           Data.List.Extra                  ( concatUnzip )
import qualified Data.List.NonEmpty               as NonEmpty
import qualified Data.Map.Strict                  as Map
import           Data.Maybe                       ( catMaybes, fromJust )
import qualified Data.Set                         as Set
import qualified Data.Text                        as Text

import qualified FreeC.Backend.Coq.Base           as Coq.Base
import           FreeC.Backend.Coq.Converter.Arg
import           FreeC.Backend.Coq.Converter.Free
import           FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Syntax         as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.Fresh
  ( freshArgPrefix, freshCoqIdent, freshCoqQualid, freshHaskellIdent )
import           FreeC.Environment.LookupOrFail
import           FreeC.Environment.Renamer        ( renameAndDefineTypeVar )
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
-- | Converts a strongly connected component of the type dependency graph and
--   creates a separate lit of qualified smart constructor notations.
convertTypeComponent :: DependencyComponent IR.TypeDecl
                     -> Converter ([Coq.Sentence], [Coq.Sentence])
convertTypeComponent (NonRecursive decl)
  | isTypeSynDecl decl = flip (,) [] <$> convertTypeSynDecl decl
  | otherwise = convertDataDecls [decl]
convertTypeComponent (Recursive decls)   = do
  let (typeSynDecls, dataDecls) = partition isTypeSynDecl decls
      typeSynDeclQNames         = Set.fromList
        (map IR.typeDeclQName typeSynDecls)
  sortedTypeSynDecls <- sortTypeSynDecls typeSynDecls
  expandedDataDecls <- mapM
    (expandAllTypeSynonymsInDeclWhere (`Set.member` typeSynDeclQNames))
    dataDecls
  (dataDecls', qualSmartConDecls) <- convertDataDecls expandedDataDecls
  typeSynDecls' <- concatMapM convertTypeSynDecl sortedTypeSynDecls
  return (dataDecls' ++ typeSynDecls', qualSmartConDecls)

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
-- | Type synonym for a map mapping types to function names.
type TypeMap = Map.Map IR.Type Coq.Qualid

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
--   is one @Arguments@ sentence and several smart constructor @Notation@
--   declarations for each constructor declaration of the given data types.
--   Qualified smart constructor notations are packed into a separate list.
convertDataDecls :: [IR.TypeDecl] -> Converter ([Coq.Sentence], [Coq.Sentence])
convertDataDecls dataDecls = do
  (indBodies, extraSentences') <- mapAndUnzipM convertDataDecl dataDecls
  let (extraSentences, qualSmartConDecls) = concatUnzip extraSentences'
  instances <- generateTypeclassInstances dataDecls
  return
    ( Coq.comment ("Data type declarations for "
                   ++ showPretty (map IR.typeDeclName dataDecls))
        : Coq.InductiveSentence (Coq.Inductive (NonEmpty.fromList indBodies) [])
        : extraSentences ++ instances
    , qualSmartConDecls
    )

-- | Converts a Haskell data type declaration to the body of a Coq @Inductive@
--   sentence, the @Arguments@ sentences for it's constructors and the smart
--   constructor notations and creates an induction scheme.
--   Qualified smart constructor notations are packed into a separate list.
--
--   Type variables declared by the data type or the smart constructors are
--   not visible outside of this function.
convertDataDecl
  :: IR.TypeDecl -> Converter (Coq.IndBody, ([Coq.Sentence], [Coq.Sentence]))
convertDataDecl (IR.DataDecl _ (IR.DeclIdent _ name) typeVarDecls conDecls) = do
  (body, argumentsSentences) <- generateBodyAndArguments
  (smartConDecls, qualSmartConDecls)
    <- concatUnzip <$> mapM generateSmartConDecl conDecls
  inductionScheme <- generateInductionScheme
  return ( body
         , ( Coq.commentedSentences
               ("Arguments sentences for " ++ showPretty (IR.toUnQual name))
               argumentsSentences
               ++ Coq.commentedSentences
               ("Induction scheme for " ++ showPretty (IR.toUnQual name))
               inductionScheme
               ++ Coq.commentedSentences
               ("Smart constructors for " ++ showPretty (IR.toUnQual name))
               smartConDecls
             , Coq.commentedSentences ("Qualified smart constructors for "
                                       ++ showPretty (IR.toUnQual name))
               qualSmartConDecls
             )
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

  -- | Generates the smart constructor notations for the given constructor
  --   declaration.
  --   There is a notation for normal application and explicit application of
  --   the smart constructor and for qualified and unqualified access. The
  --   unqualified notations form the first list and the qualified notations
  --   form the second list.
  generateSmartConDecl
    :: IR.ConDecl -> Converter ([Coq.Sentence], [Coq.Sentence])
  generateSmartConDecl (IR.ConDecl _ declIdent argTypes) = localEnv $ do
    let conName = IR.declIdentName declIdent
    mbModName <- inEnv $ lookupModName IR.ValueScope conName
    Just qualid <- inEnv $ lookupIdent IR.ValueScope conName
    Just smartQualid <- inEnv $ lookupSmartIdent conName
    Just returnType <- inEnv $ lookupReturnType IR.ValueScope conName
    constrArgIdents <- mapM (const $ freshCoqIdent freshArgPrefix) argTypes
    let Just unqualIdent = Coq.unpackQualid smartQualid
    typeVarQualids <- mapM
      (\(IR.TypeVarDecl srcSpan ident) -> renameAndDefineTypeVar srcSpan ident)
      typeVarDecls
    let typeVarIdents = map (fromJust . Coq.unpackQualid) typeVarQualids
    returnType' <- convertType' returnType
    -- Generate unqualified and qualified notation sentences for the smart
    -- constructor if possible.
    return
      ( generateSmartConDecl' unqualIdent qualid typeVarIdents constrArgIdents
          returnType'
      , case mbModName of
          Just modName -> generateSmartConDecl' (modName ++ '.' : unqualIdent)
            qualid typeVarIdents constrArgIdents returnType'
          Nothing      -> []
      )

  -- | Generates a notation sentence for the smart constructor and the
  --   explicit application of the smart constructor.
  generateSmartConDecl'
    :: String
    -> Coq.Qualid
    -> [String]
    -> [String]
    -> Coq.Term
    -> [Coq.Sentence]
  generateSmartConDecl' smartIdent constr typeVarIdents constrArgIdents
    expReturnType = [ Coq.notationSentence lhs rhs mods
                    , Coq.notationSentence expLhs expRhs expMods
                    ]
   where
    freeArgIdents = map (fromJust . Coq.unpackQualid . fst) Coq.Base.freeArgs

    freeArgs      = map (Coq.Qualid . fst) Coq.Base.freeArgs

    -- Default smart constructor with implicit type args.
    returnType    = case expReturnType of
      (Coq.App tcon (shape NonEmpty.:| pos : tvars))
        | length tvars == length typeVarIdents -> Coq.App tcon
          (shape NonEmpty.:| pos
           : map (Coq.PosArg . const Coq.Underscore) tvars)
      _ -> Coq.Underscore

    argIdents     = freeArgIdents ++ constrArgIdents

    args          = freeArgs
      ++ map (const Coq.Underscore) typeVarIdents
      ++ map (Coq.Qualid . Coq.bare) constrArgIdents

    lhs           = Coq.nSymbol smartIdent NonEmpty.:| map Coq.nIdent argIdents

    rhs           = Coq.explicitApp Coq.Base.freePureCon
      $ freeArgs ++ [returnType, Coq.explicitApp constr args]

    mods          = [ Coq.sModLevel 10
                    , Coq.sModIdentLevel (NonEmpty.fromList argIdents) (Just 9)
                    ]

    -- Explicit notation for the smart constructor.
    expArgIdents  = freeArgIdents ++ typeVarIdents ++ constrArgIdents

    expArgs       = map (Coq.Qualid . Coq.bare) expArgIdents

    expLhs        = Coq.nSymbol ('@' : smartIdent)
      NonEmpty.:| map Coq.nIdent expArgIdents

    expRhs        = Coq.explicitApp Coq.Base.freePureCon
      $ freeArgs ++ [expReturnType, Coq.explicitApp constr expArgs]

    expMods
      = [ Coq.SModOnlyParsing
        , Coq.sModLevel 10
        , Coq.sModIdentLevel (NonEmpty.fromList expArgIdents) (Just 9)
        ]

  -- | Generates an induction scheme for the data type.
  generateInductionScheme :: Converter [Coq.Sentence]
  generateInductionScheme = localEnv $ do
    Just tIdent <- inEnv $ lookupIdent IR.TypeScope name
    -- Create variables and binders.
    let generateArg :: Coq.Term -> Converter (Coq.Qualid, Coq.Binder)
        generateArg argType = do
          ident <- freshCoqQualid freshArgPrefix
          return
            $ ( ident
              , Coq.typedBinder Coq.Ungeneralizable Coq.Explicit [ident] argType
              )
    (tvarIdents, tvarBinders) <- convertTypeVarDecls' Coq.Explicit typeVarDecls
    (propIdent, propBinder) <- generateArg
      (Coq.Arrow (genericApply tIdent [] [] (map Coq.Qualid tvarIdents))
       (Coq.Sort Coq.Prop))
    (_hIdents, hBinders) <- mapAndUnzipM (generateInductionCase propIdent)
      conDecls
    (valIdent, valBinder) <- generateArg
      (genericApply tIdent [] [] (map Coq.Qualid tvarIdents))
    -- Stick everything together.
    schemeName <- freshCoqQualid $ fromJust (Coq.unpackQualid tIdent) ++ "_Ind"
    hypothesisVar <- freshCoqIdent "H"
    let binders = genericArgDecls Coq.Explicit
          ++ tvarBinders
          ++ [propBinder]
          ++ hBinders
        term    = Coq.Forall (NonEmpty.fromList [valBinder])
          (Coq.app (Coq.Qualid propIdent) [Coq.Qualid valIdent])
        scheme  = Coq.Assertion Coq.Definition schemeName binders term
        proof   = Coq.ProofDefined
          (Text.pack
           $ "  fix "
           ++ hypothesisVar
           ++ " 1; intro; "
           ++ fromJust (Coq.unpackQualid Coq.Base.proveInd)
           ++ ".")
    return [Coq.AssertionSentence scheme proof]

  -- | Generates an induction case for a given property and constructor.
  generateInductionCase
    :: Coq.Qualid -> IR.ConDecl -> Converter (Coq.Qualid, Coq.Binder)
  generateInductionCase pIdent (IR.ConDecl _ declIdent argTypes) = do
    let conName = IR.declIdentName declIdent
    Just conIdent <- inEnv $ lookupIdent IR.ValueScope conName
    Just conType' <- inEnv $ lookupReturnType IR.ValueScope conName
    conType <- convertType' conType'
    fConType <- convertType conType'
    fArgTypes <- mapM convertType argTypes
    (argIdents, argBinders) <- mapAndUnzipM convertAnonymousArg
      (map Just argTypes)
    let 
      -- We need an induction hypothesis for every argument that has the same
      -- type as the constructor but lifted into the free monad.
      addHypotheses' :: [(Coq.Term, Coq.Qualid)] -> Coq.Term -> Coq.Term
      addHypotheses' [] = id
      addHypotheses' ((argType, argIdent) : args)
        | argType == fConType = Coq.Arrow
          (genericForFree conType pIdent argIdent)
          . addHypotheses' args
      addHypotheses' (_ : args) = addHypotheses' args
      addHypotheses = addHypotheses' (zip fArgTypes argIdents)
      -- Create induction case.
      term = addHypotheses
        (Coq.app (Coq.Qualid pIdent)
         [Coq.app (Coq.Qualid conIdent) (map Coq.Qualid argIdents)])
      indCase = if null argBinders
        then term
        else Coq.Forall (NonEmpty.fromList argBinders) term
    indCaseIdent <- freshCoqQualid freshArgPrefix
    indCaseBinder <- generateArgBinder indCaseIdent (Just indCase)
    return (indCaseIdent, indCaseBinder)
-- Type synonyms are not allowed in this function.
convertDataDecl (IR.TypeSynDecl _ _ _ _)
  = error "convertDataDecl: Type synonym not allowed."

-------------------------------------------------------------------------------
-- Instance Generation                                                       --
-------------------------------------------------------------------------------
-- | Builds instances for all supported typeclasses.
--   Currently, only a @Normalform@ instance is generated.
--
--   Suppose we have a type
--   > data T a1 ... an = C1 a11 ... a1m1 | ... | Ck ak1 ... akmk.
--   We wish to generate an instance of class @C@ providing the function
--   @f : T a1 ... an -> B@, where @B@ is a type.
--   For example, for the @Normalform@ class, @f@ would be
--   > nf' : T a1 ... an -> Free Shape Pos (T a1 ... an).
--
--   The generated function has the following basic structure:
--
--   > f'T < class-specific binders > (x : T a1 ... an) : B
--   >      := match x with
--   >         | C1 fx11 ... fx1m1 => < buildValue x [fx11, ..., fx1m1] >
--   >         | ...
--   >         | Ck fxk1 ... fxkmk => < buildValue x [fxk1, ..., fxkmk] >
--   >         end.
--
--   @buildValue x [fxi1, ..., fximi]@ represents class-specific code that
--   actually constructs a value of type @B@ when given @x@ and the
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
--   A directly recursive argument has the type @T t1 ... tn@, where @ti@ are
--   type expressions (not necessarily type variables). We assume that @ti'@
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
--   The problem is solved by introducing a local function fT' for every type
--   @T'@ that contains @T@ that inlines the definition of a @T'@ instance of
--   @C@, and call this functions for arguments of type @T'@.
--   These local functions are as polymorphic as possible to reduce the number
--   of local functions we need.
--
--   For example, if we want to generate an instance for the Haskell type
--   @data Forest a = AForest [Forest a]
--                  | IntForest [Forest Int]
--                  | BoolForest [ForestBool]@,
--   only one local function is needed.
--   @fListForest_ : List Shape Pos (Forest Shape Pos a)
--                -> Free Shape Pos (List Identity.Shape Identity.Pos
--                                    (Forest Identity.Shape Identity.Pos b))@
--
--   To generate these local function, for every type expression @aij@ in the
--   constructors of @T@, we collect all types that contain the original type
--   @T@.
--   More specifically, a type expression @T' t1 ... tm@ is collected if
--   @ti = T t1' ... tn'@ for some type expressions @t1', ..., tn'@, or if @ti@
--   is collected for some @i@.
--   During this process, any type expression that does not contain @T@ is
--   replaced by a placeholder variable "_".
--
--   We keep track of which types correspond to which function with a map.
--
--   The generated functions @fT1, ..., fTn@ for @n@ mutually recursive types
--   @T1, ... Tn@ are a set of @n@ @Fixpoint@ definitions linked with @with@.
--   Indirectly recursive types and local functions based on them are computed
--   for each type.
--   In this case, a type @T'@ is considered indirectly recursive if it
--   contains any of the types @T1, ..., Tn@.
--   Arguments of type @Ti@ can be treated like directly recursive arguments.
generateTypeclassInstances :: [IR.TypeDecl] -> Converter [Coq.Sentence]
generateTypeclassInstances dataDecls = do
  -- The types of the data declaration's constructors' arguments.
  let argTypes = map (concatMap IR.conDeclFields . IR.dataDeclCons) dataDecls
  -- The same types where all type synonyms are expanded.
  argTypesExpanded
    <- mapM (mapM expandAllTypeSynonyms) argTypes -- :: [[IR.Type]]
  -- A list where all fully-applied type constructors that do not contain one of the types
  -- for which we are defining instances and all type variables are replaced with
  -- the same type variable (an underscore). The list is reversed so its entries are
  -- in topological order.
  let reducedTypes = map (nub . reverse . concatMap collectSubTypes)
        argTypesExpanded
  -- Like reducedTypes, but with all occurrences of the types for which we are defining
  -- instances and all type variables removed from the list.
  -- This leaves exactly the types with indirect recursion, with all non-recursive
  -- components replaced by underscores.
  let recTypeList = map
        (filter (\t -> not (t `elem` declTypes || IR.isTypeVar t))) reducedTypes
  -- Construct Normalform instances.
  buildInstances recTypeList normalformFuncName normalformClassName
    nfBindersAndReturnType buildNormalformValue
 where
  -- The (mutually recursive) data types for which we are defining
  -- instances, converted to types.
  declTypes :: [IR.Type]
  declTypes = map dataDeclToType dataDecls

  -- The names of the constructors of the data types for which
  -- we are defining instances.
  conNames :: [IR.TypeConName]
  conNames = map IR.typeDeclQName dataDecls

  -- | Constructs instances of a typeclass for a set of mutually recursive
  --   types. The typeclass is specified by the arguments.
  buildInstances
    ::
    -- For each data declaration, this list contains the occurrences of
    -- indirect recursion in the constructors of that data declaration.
    [[IR.Type]]
    -> String -- The name of the class function.
    -> String -- The name of the typeclass.
    -> (IR.Type -- The type for which the instance is being defined.
        -> Coq.Qualid -- The name of a variable of that type.
        -> Converter ([Coq.Binder], Coq.Binder, Coq.Term, Coq.Term))
    -> (TypeMap -- A mapping from types to function names.
        -> Coq.Qualid -- The name of a constructor.
        -> [(IR.Type, Coq.Qualid)]
        -> Converter Coq.Term)
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
      ::
      -- A map to map occurrences of the top-level types to recursive
      -- function calls.
      TypeMap -> IR.Type -> [IR.Type] -> Converter (Coq.FixBody, Coq.Sentence)
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
      ::
      -- A mapping from (indirectly) recursive types to function names.
      TypeMap -> IR.Type -> [Coq.Binder] -> Coq.Term -> Converter Coq.Sentence
    buildInstance m t binders retType = do
      -- Define the class function as the function to which the current type
      -- is mapped.
      let instanceBody
            = (Coq.bare functionPrefix, Coq.Qualid (fromJust (Map.lookup t m)))
      instanceName <- Coq.bare <$> nameFunction className t
      return
        $ Coq.InstanceSentence
        (Coq.InstanceDefinition instanceName (freeArgsBinders ++ binders)
         retType [instanceBody] Nothing)

    -- | Generates the implementation of the body of a class function for the
    --   given type.
    makeFixBody
      ::
      -- A mapping from (indirectly or directly) recursive types to the name
      -- of the function that handles arguments of those types.
      TypeMap
      -> Coq.Qualid
      -> IR.Type
      -> [Coq.Binder]
      -> Coq.Term
      -> [IR.Type]
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
      :: TypeMap -> Coq.Qualid -> IR.Type -> [IR.Type] -> Converter Coq.Term

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
      -- Then convert all irrelevant components into underscores again so the
      -- type can be looked up in the type map.
      expandedArgTypes <- mapM expandAllTypeSynonyms (entryArgTypes conEntry)
      let modArgTypes = map (stripType . applySubst subst) expandedArgTypes
      let lhs = Coq.ArgsPat conIdent (map Coq.QualidPat conArgIdents)
      -- Build the right-hand side of the equation by applying the
      -- class-specific function buildValue.
      rhs <- buildValue m conIdent (zip modArgTypes conArgIdents)
      return $ Coq.equation lhs rhs

  -------------------------------------------------------------------------------
  -- Typeclass-specific Functions                                              --
  -------------------------------------------------------------------------------
  -------------------------------------------------------------------------------
  -- Functions to produce Normalform instances                                 --
  -------------------------------------------------------------------------------
  -- | The name of the Normalform class.
  normalformClassName :: String
  normalformClassName = "Normalform"

  -- | The name of the Normalform class function.
  normalformFuncName :: String
  normalformFuncName = "nf'"

  -- | The binders and return types for the Normalform class function and instance.
  nfBindersAndReturnType
    ::
    -- The type for which we are defining an instance.
    IR.Type
    -> Coq.Qualid
    -> Converter
    ( [Coq.Binder] -- Type variable binders and Normalform constraints.
    , Coq.Binder -- Binder for the argument of type @t@.
    , Coq.Term -- Return type of nf'.
    , Coq.Term
    ) -- Return type of the Normalform instance.

  nfBindersAndReturnType t varName = do
    -- For each type variable in the type, generate two type variables.
    -- One represents the type's variable itself, the other the result
    -- type of the normalization.
    -- The type is transformed to a Coq type twice, once with Shape and
    -- Pos as arguments for the original type, once with Identity.Shape
    -- and Identity.Pos as arguments for the normalized result type.
    (sourceType, sourceVars) <- toCoqType "a" shapeAndPos t
    (targetType, targetVars) <- toCoqType "b" idShapeAndPos t
    -- For each type variable ai, build a constraint
    -- `{Normalform Shape Pos ai bi}.
    let constraints = map (buildConstraint normalformClassName)
          (zipWith (\v1 v2 -> [v1, v2]) sourceVars targetVars)
    let varBinders
          = [typeVarBinder (sourceVars ++ targetVars) | not (null sourceVars)]
    let binders = varBinders ++ constraints
    -- Create an explicit argument binder for the value to be normalized.
    let topLevelVarBinder
          = Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit varName sourceType
    let instanceRetType = Coq.app (Coq.Qualid (Coq.bare normalformClassName))
          (shapeAndPos ++ [sourceType, targetType])
    let funcRetType = applyFree targetType
    return (binders, topLevelVarBinder, funcRetType, instanceRetType)

  -- | Builds a normalized @Free@ value for the given constructor
  --   and constructor arguments.
  buildNormalformValue
    ::
    -- A map to associate types with the appropriate functions to call.
    TypeMap -> Coq.Qualid -> [(IR.Type, Coq.Qualid)] -> Converter Coq.Term
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
            $ applyBind
            (Coq.app (Coq.Qualid (Coq.bare "nf")) [Coq.Qualid varName]) c

  -------------------------------------------------------------------------------
  -- Helper functions                                                          --
  -------------------------------------------------------------------------------
  -- | Creates an entry with a unique name for each of the given types and
  --   inserts them into the given map.
  nameFunctionsAndInsert :: String -> TypeMap -> [IR.Type] -> Converter TypeMap
  nameFunctionsAndInsert prefix = foldM (nameFunctionAndInsert prefix)

  -- | Like `nameFunctionsAndInsert`, but for a single type.
  nameFunctionAndInsert :: String -> TypeMap -> IR.Type -> Converter TypeMap
  nameFunctionAndInsert prefix m t = do
    name <- nameFunction prefix t
    return (Map.insert t (Coq.bare name) m)

  -- | Names a function based on a type expression while avoiding name clashes
  --   with other identifiers.
  nameFunction :: String -> IR.Type -> Converter String
  nameFunction prefix t = do
    prettyType <- showPrettyType t
    freshCoqIdent (prefix ++ prettyType)

  -- | A type variable that represents irrelevant parts of a type expression.
  -- Represented by an underscore.
  placeholderVar :: IR.Type
  placeholderVar = IR.TypeVar NoSrcSpan "_"

  -- | Collects all fully-applied type constructors
  --   of arity at least 1 (including their arguments) that occur in the given
  --   type. All arguments that do not contain occurrences of the types for
  --   which we are defining an instance are replaced by the type variable "_".
  --   The resulting list contains (in reverse topological order) exactly all
  --   types for which we must define a separate function in the instance
  --   definition, where all occurrences of "_" represent the polymorphic
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
  --   by the type variable "_".
  stripType :: IR.Type -> IR.Type
  stripType t = stripType' t False
   where
    -- | Like 'stripType', but with an additional flag to denote whether an
    --   occurrence of a relevant type was found in an argument of a type
    --   application.
    --   This is necessary so that, for example, @Pair Bool t@ is not
    --   translated to @_ t@, but to @Pair _ t@.
    stripType' :: IR.Type -> Bool -> IR.Type

    --
    stripType' (IR.TypeCon _ conName) flag
      | flag || conName `elem` conNames = IR.TypeCon NoSrcSpan conName
      | otherwise = placeholderVar
    -- For a type application, check if a relevant type occurs in @r@.
    stripType' (IR.TypeApp _ l r) flag = case stripType' r False of
      -- If not, check if a relevant type occurs in @l@, and otherwise
      -- replace the whole expression with an underscore.
      r'@(IR.TypeVar _ _) -> case stripType' l flag of
        IR.TypeVar _ _ -> placeholderVar
        l'             -> IR.TypeApp NoSrcSpan l' r'
      -- If a relevant type does occur in @r@, the type application must
      -- be preserved, so only its arguments are stripped.´
      r'                  -> IR.TypeApp NoSrcSpan (stripType' l True) r'
    -- Type variables and function types are not relevant and are replaced by "_".
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

  -- | Converts a data declaration to a type by applying its constructor to the
  --   correct number of variables, denoted by underscores.
  dataDeclToType :: IR.TypeDecl -> IR.Type
  dataDeclToType dataDecl = IR.typeConApp NoSrcSpan (IR.typeDeclQName dataDecl)
    (replicate (length (IR.typeDeclArgs dataDecl)) placeholderVar)

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
  -- > freeArgsBinders = [ {Shape : Type}, {Pos : Shape -> Type} ]
  freeArgsBinders :: [Coq.Binder]
  freeArgsBinders = genericArgDecls Coq.Implicit

  -- | Shortcut for the construction of an implicit binder for type variables.
  --   > typeVarBinder [a1, ..., an] = {a1 ... an : Type}
  typeVarBinder :: [Coq.Qualid] -> Coq.Binder
  typeVarBinder typeVars
    = Coq.typedBinder Coq.Ungeneralizable Coq.Implicit typeVars Coq.sortType

  -- | Constructs a type class constraint.
  --   > buildConstraint name [a1 ... an] = `{name Shape Pos a1 ... an}.
  buildConstraint :: String -> [Coq.Qualid] -> Coq.Binder
  buildConstraint className args = Coq.Generalized Coq.Implicit
    (Coq.app (Coq.Qualid (Coq.bare className))
     (shapeAndPos ++ map Coq.Qualid args))

  -- | Shortcut for the application of >>=.
  applyBind :: Coq.Term -> Coq.Term -> Coq.Term
  applyBind mx f = Coq.app (Coq.Qualid Coq.Base.freeBind) [mx, f]

  -- | Given an A, returns Free Shape Pos A
  applyFree :: Coq.Term -> Coq.Term
  applyFree a = Coq.app (Coq.Qualid Coq.Base.free) (shapeAndPos ++ [a])

  -- | Shape and Pos arguments as Coq terms.
  shapeAndPos :: [Coq.Term]
  shapeAndPos = [Coq.Qualid Coq.Base.shape, Coq.Qualid Coq.Base.pos]

  -- | The shape and position function arguments for the Identity monad
  --   as a Coq term.
  idShapeAndPos :: [Coq.Term]
  idShapeAndPos = map Coq.Qualid
    [ Coq.Qualified (Coq.ident "Identity") Coq.Base.shapeIdent
    , Coq.Qualified (Coq.ident "Identity") Coq.Base.posIdent
    ]

  -- | Converts a type into a Coq type (a term) with the specified
  --   additional arguments (for example Shape and Pos) and fresh Coq
  --   identifiers for all underscores.
  --   Returns a pair of the result term and a list of the fresh variables.
  toCoqType :: String -- The prefix of the fresh variables.
            -> [Coq.Term] -- A list of additional arguments, e.g. Shape and Pos.
            -> IR.Type -- The type to convert.
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
