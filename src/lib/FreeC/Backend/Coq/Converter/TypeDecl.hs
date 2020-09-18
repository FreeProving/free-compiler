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

import           Control.Monad                    ( mapAndUnzipM )
import           Control.Monad.Extra              ( concatMapM )
import           Data.List                        ( partition )
import           Data.List.Extra                  ( concatUnzip )
import qualified Data.List.NonEmpty               as NonEmpty
import           Data.Maybe                       ( catMaybes, fromJust, fromMaybe )
import qualified Data.Map                         as Map
import qualified Data.Set                         as Set
import qualified Data.Text                        as Text

import qualified FreeC.Backend.Coq.Base           as Coq.Base
import           FreeC.Backend.Coq.Converter.Arg
import           FreeC.Backend.Coq.Converter.Free
import           FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Syntax         as Coq
import           FreeC.Environment
import           FreeC.Environment.Fresh
  ( freshArgPrefix, freshCoqIdent, freshCoqQualid )
import           FreeC.Environment.Renamer        ( renameAndDefineTypeVar )
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax                  as IR
import           FreeC.IR.TypeSynExpansion
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
  inductionSentences <- generateInductionSchemes dataDecls
  let (extraSentences, qualSmartConDecls) = concatUnzip extraSentences'
  return
    ( Coq.comment ("Data type declarations for "
                   ++ showPretty (map IR.typeDeclName dataDecls))
        : Coq.InductiveSentence (Coq.Inductive (NonEmpty.fromList indBodies) [])
        : extraSentences ++ inductionSentences
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
  return ( body
         , ( Coq.commentedSentences
               ("Arguments sentences for " ++ showPretty (IR.toUnQual name))
               argumentsSentences
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

-- Type synonyms are not allowed in this function.
convertDataDecl (IR.TypeSynDecl _ _ _ _)
  = error "convertDataDecl: Type synonym not allowed."

generateInductionSchemes :: [IR.TypeDecl] -> Converter [Coq.Sentence]
generateInductionSchemes dataDecls = do
  forQualidMap <- Map.fromList <$> mapM (generateForName . IR.typeDeclQName) dataDecls
  forBodies <- catMaybes <$> mapM (generateForProperty forQualidMap) dataDecls
  {-}
  inBodies  <- return [] -- generateInProperties
  inductionSentences <- return [] -- generateInductionSchemes'
  forallSentences <- return [] -- generateForallSentences-}
  return [Coq.InductiveSentence (Coq.Inductive (NonEmpty.fromList forBodies) []) | not (null forBodies)]
 where

  generateForName :: IR.QName -> Converter (IR.QName, Coq.Qualid)
  generateForName typeQName = do
    Just typeQualid <- inEnv $ lookupIdent IR.TypeScope typeQName
    let Just typeIdent = Coq.unpackQualid typeQualid
    forQualid <- freshCoqQualid $ "For" ++ typeIdent
    return (typeQName, forQualid)

  generateForConName :: Coq.Qualid -> IR.QName -> Converter Coq.Qualid
  generateForConName forTypeQualid conQName = do
    Just conQualid <- inEnv $ lookupIdent IR.ValueScope conQName
    let Just forTypeName = Coq.unpackQualid forTypeQualid
        Just conName     = Coq.unpackQualid conQualid 
    freshCoqQualid $ forTypeName ++ "_" ++ conName

  generateForProperty :: Map.Map IR.QName Coq.Qualid -> IR.TypeDecl -> Converter (Maybe Coq.IndBody)
  generateForProperty _ (IR.TypeSynDecl _ _ _ _) = error "generateForProperty: Type synonym not allowed"
  generateForProperty _ (IR.DataDecl _ _ [] _) = return Nothing -- Types without out type variable do not need a 'For-' property
  generateForProperty forQualidMap (IR.DataDecl _ (IR.DeclIdent _ typeName) typeVarDecls conDecls) = do
    Just typeQualid <- inEnv $ lookupIdent IR.TypeScope typeName
    let forQualid = forQualidMap Map.! typeName
    forConQualids <- mapM (generateForConName forQualid . IR.conDeclQName) conDecls
    localEnv $ do
      (typeVarQualids, typeVarBinders) <- convertTypeVarDecls' Coq.Explicit typeVarDecls
      propertyQualids <- mapM  (const $ freshCoqQualid "P") typeVarQualids
      forCons <- mapM (uncurry (generateForConstructor typeVarQualids propertyQualids)) $ zip conDecls forConQualids
      let propertyTypes = map  (\a -> (Coq.Arrow (Coq.Qualid a) (Coq.Sort Coq.Prop))) typeVarQualids
          propertyBinders = map (\(a,t) -> Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit a t) $ zip propertyQualids propertyTypes
          binders = genericArgDecls Coq.Explicit ++ typeVarBinders ++ propertyBinders
          returnType = Coq.Arrow (Coq.app (Coq.Qualid typeQualid) (map Coq.Qualid (map fst Coq.Base.freeArgs ++ typeVarQualids)))
                             (Coq.Sort Coq.Prop)
      return $ Just $ Coq.IndBody forQualid binders returnType forCons
   where
    generateForConstructor :: [Coq.Qualid] -> [Coq.Qualid] -> IR.ConDecl -> Coq.Qualid -> Converter (Coq.Qualid, [Coq.Binder], Maybe Coq.Term)
    generateForConstructor typeVarQualids propertyQualids (IR.ConDecl _ (IR.DeclIdent _ conName) args) forConQualid = do
      Just conQualid <- inEnv $ lookupIdent IR.ValueScope conName
      (argQualids, binders) <- unzip <$> mapM (convertAnonymousArg . Just) args
      forHypotheses <- catMaybes <$> (mapM (uncurry generateForHypothesis) $ zip argQualids args)
      let forQualid = forQualidMap Map.! typeName
          forResult = Coq.app (Coq.Qualid forQualid)
            (   map (Coq.Qualid . fst) Coq.Base.freeArgs
             ++ map Coq.Qualid typeVarQualids
             ++ map Coq.Qualid propertyQualids
             ++ [genericApply conQualid [] (map Coq.Qualid typeVarQualids) (map Coq.Qualid argQualids)])
          returnType = Coq.forall binders (foldr Coq.Arrow forResult forHypotheses)
      return (forConQualid, [], Just returnType)
     where
      propertyMap :: Map.Map Coq.Qualid Coq.Qualid
      propertyMap = Map.fromList $ zip typeVarQualids propertyQualids

      generateForHypothesis :: Coq.Qualid -> IR.Type -> Converter (Maybe Coq.Term)
      generateForHypothesis argQualid argType = do
        coqType  <- convertType' argType
        argType' <- expandAllTypeSynonyms argType
        mbHyp <- generateForHypothesis_1 argType'
        return $ case mbHyp of
          Just hyp -> Just $ Coq.app (Coq.Qualid Coq.Base.forFree) (map (Coq.Qualid . fst) Coq.Base.freeArgs ++ [coqType, hyp, Coq.Qualid argQualid])
          Nothing  -> Nothing
        
      generateForHypothesis_1 :: IR.Type -> Converter (Maybe Coq.Term)
      generateForHypothesis_1 (IR.FuncType _ _ _) = return Nothing
      generateForHypothesis_1 (IR.TypeApp _ tcon lastArg) = generateForHypothesis_2 tcon [lastArg]
      generateForHypothesis_1 (IR.TypeCon _ _)    = return Nothing -- Ignore type vars that do not have any type variable or are partially applied
      generateForHypothesis_1 tvar@(IR.TypeVar _ _) = do
        Coq.Qualid tvarQualid <- convertType' tvar
        return $ Coq.Qualid <$> propertyMap Map.!? tvarQualid

      generateForHypothesis_2 :: IR.Type -> [IR.Type] -> Converter (Maybe Coq.Term)
      generateForHypothesis_2 (IR.FuncType _ _ _) _ = return Nothing
      generateForHypothesis_2 (IR.TypeApp _ tcon lastArg) typeArgs = generateForHypothesis_2 tcon (lastArg : typeArgs)
      generateForHypothesis_2 (IR.TypeCon _ tconName) typeArgs = do
        Just tconArity <- inEnv $ lookupArity IR.TypeScope tconName
        hypotheses <- mapM generateForHypothesis_1 typeArgs
        coqArgs <- mapM convertType' typeArgs
        forType <- getForType tconName
        if (tconArity == length typeArgs) && (not $ null $ catMaybes hypotheses)
          then do let hypotheses' = map (fromMaybe (Coq.Qualid Coq.Base.noProperty)) hypotheses
                  return $ Just $ Coq.app forType (map (Coq.Qualid . fst) Coq.Base.freeArgs ++ coqArgs ++ hypotheses')
          else return Nothing
      generateForHypothesis_2 (IR.TypeVar _ _) _ = return Nothing

      getForType :: IR.QName -> Converter Coq.Term
      getForType t = case forQualidMap Map.!? t of
        Just qualid -> return $ Coq.Qualid qualid
        Nothing -> do
          -- TODO use environment to store and load other 'For-' properties
          Just qualid <- inEnv $ lookupIdent IR.TypeScope t
          let name = case qualid of
                Coq.Bare n -> Text.unpack n
                Coq.Qualified _ n -> Text.unpack n
          return $ Coq.Qualid $ Coq.bare $ "For" ++ name
{-}
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
-}