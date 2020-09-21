module FreeC.Backend.Coq.Converter.TypeDecl.InductionScheme where

import           Control.Monad                    ( mapAndUnzipM )
import           Control.Monad.Extra              ( concatMapM )
import qualified Data.List.NonEmpty               as NonEmpty
import           Data.Maybe                       ( catMaybes, fromMaybe, fromJust )
import qualified Data.Map                         as Map
import qualified Data.Text                        as Text

import qualified FreeC.Backend.Coq.Base           as Coq.Base
import           FreeC.Backend.Coq.Converter.Arg
import           FreeC.Backend.Coq.Converter.Free
import           FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Syntax         as Coq
import           FreeC.Environment
import           FreeC.Environment.Fresh
  ( freshArgPrefix, freshCoqQualid )
import qualified FreeC.IR.Syntax                  as IR
import           FreeC.IR.TypeSynExpansion
import           FreeC.Monad.Converter

--import FreeC.Pretty
--import Text.PrettyPrint.Leijen.Text ( (<+>) )
--import Debug.Trace

generateInductionSchemes :: [IR.TypeDecl] -> Converter [Coq.Sentence]
generateInductionSchemes dataDecls = do
  let complexDataDecls = filter hasTypeVar dataDecls
  forQualidMap <- Map.fromList <$> mapM (generateName "For" "" . IR.typeDeclQName) complexDataDecls
  forBodies <- mapM (generateForProperty forQualidMap) complexDataDecls
  inQualidMap <- Map.fromList <$> mapM (generateInNames . IR.typeDeclQName) complexDataDecls
  inBodies  <- concatMapM (generateInProperties inQualidMap) complexDataDecls
  schemeQualidMap <- Map.fromList <$> mapM (generateName "" "_Ind" . IR.typeDeclQName) dataDecls
  schemeBodies <- mapM (generateSchemeLemma schemeQualidMap forQualidMap) dataDecls
  forallQualidMap <- Map.fromList <$> mapM (generateName "For" "_forall". IR.typeDeclQName) complexDataDecls
  forallBodies <- mapM (generateForallLemma forallQualidMap forQualidMap inQualidMap) dataDecls
  return
    ( [Coq.InductiveSentence (Coq.Inductive (NonEmpty.fromList forBodies) []) | not (null forBodies)]
    ++[Coq.InductiveSentence (Coq.Inductive (NonEmpty.fromList inBodies) []) | not (null inBodies)]
    ++(map (\(name, binders, term, proof) ->
              Coq.AssertionSentence (Coq.Assertion Coq.Lemma name binders term) proof) (schemeBodies ++ forallBodies))
    )
 where

  -----------------------------------------------------------------------------
  -- @ForType@ Properties                                                    --
  -----------------------------------------------------------------------------

  generateForProperty :: Map.Map IR.QName Coq.Qualid -> IR.TypeDecl -> Converter Coq.IndBody
  generateForProperty _ (IR.TypeSynDecl _ _ _ _) = error "generateForProperty: Type synonym not allowed"
  generateForProperty forQualidMap (IR.DataDecl _ (IR.DeclIdent _ typeName) typeVarDecls conDecls) = do
    Just typeQualid <- inEnv $ lookupIdent IR.TypeScope typeName
    let forQualid = forQualidMap Map.! typeName
    forConQualids <- mapM (generateConName forQualid . IR.conDeclQName) conDecls
    localEnv $ do
      (typeVarQualids, typeVarBinders) <- convertTypeVarDecls' Coq.Explicit typeVarDecls
      propertyQualids <- mapM  (const $ freshCoqQualid "P") typeVarQualids
      forCons <- mapM (uncurry (generateForConstructor typeVarQualids propertyQualids)) $ zip conDecls forConQualids
      let propertyTypes = map  (\a -> (Coq.Arrow (Coq.Qualid a) (Coq.Sort Coq.Prop))) typeVarQualids
          propertyBinders = map (\(a,t) -> Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit a t) $ zip propertyQualids propertyTypes
          binders = genericArgDecls Coq.Explicit ++ typeVarBinders ++ propertyBinders
          returnType = Coq.Arrow (genericApply typeQualid [] [] (map Coq.Qualid typeVarQualids))
                             (Coq.Sort Coq.Prop)
      return $ Coq.IndBody forQualid binders returnType forCons
   where
    generateForConstructor :: [Coq.Qualid] -> [Coq.Qualid] -> IR.ConDecl -> Coq.Qualid -> Converter (Coq.Qualid, [Coq.Binder], Maybe Coq.Term)
    generateForConstructor typeVarQualids propertyQualids (IR.ConDecl _ (IR.DeclIdent _ conName) args) forConQualid = localEnv $ do
      Just conQualid <- inEnv $ lookupIdent IR.ValueScope conName
      (argQualids, binders) <- unzip <$> mapM (convertAnonymousArg . Just) args
      forHypotheses <- catMaybes <$> (mapM (uncurry generateForHypothesis) $ zip argQualids args)
      let forQualid = forQualidMap Map.! typeName
          forResult = genericApply forQualid [] []
            (   map Coq.Qualid typeVarQualids
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
          Just hyp -> Just $ genericApply Coq.Base.forFree [] [] [coqType, hyp, Coq.Qualid argQualid]
          Nothing  -> Nothing
        
      generateForHypothesis_1 :: IR.Type -> Converter (Maybe Coq.Term)
      generateForHypothesis_1 (IR.FuncType _ _ _) = return Nothing
      generateForHypothesis_1 (IR.TypeApp _ tcon lastArg) = generateForHypothesis_2 tcon [lastArg]
      generateForHypothesis_1 (IR.TypeCon _ _)    = return Nothing -- Ignore type constructors that do not have any type variable or are partially applied
      generateForHypothesis_1 tvar@(IR.TypeVar _ _) = do
        Coq.Qualid tvarQualid <- convertType' tvar
        return $ Coq.Qualid <$> propertyMap Map.!? tvarQualid

      generateForHypothesis_2 :: IR.Type -> [IR.Type] -> Converter (Maybe Coq.Term)
      generateForHypothesis_2 (IR.FuncType _ _ _) _ = return Nothing
      generateForHypothesis_2 (IR.TypeApp _ tcon lastArg) typeArgs = generateForHypothesis_2 tcon (lastArg : typeArgs)
      generateForHypothesis_2 (IR.TypeCon _ tconName) typeArgs = do
        Just tconArity <- inEnv $ lookupArity IR.TypeScope tconName
        hypotheses <- mapM generateForHypothesis_1 typeArgs
        if (tconArity == length typeArgs) && (not $ null $ catMaybes hypotheses)
          then do let hypotheses' = map (fromMaybe (Coq.Qualid Coq.Base.noProperty)) hypotheses
                  coqArgs <- mapM convertType' typeArgs
                  forType <- getForType forQualidMap tconName
                  return $ Just $ genericApply forType [] [] (coqArgs ++ hypotheses')
          else return Nothing
      generateForHypothesis_2 (IR.TypeVar _ _) _ = return Nothing

  -----------------------------------------------------------------------------
  -- @InType@ Properties                                                     --
  -----------------------------------------------------------------------------

  generateInNames :: IR.QName -> Converter (IR.QName, [Coq.Qualid])
  generateInNames typeName = do
    Just arity <- inEnv $ lookupArity IR.TypeScope typeName
    inQualids <- map snd <$>  if arity == 1
      then mapM (generateName "In" "") [typeName]
      else mapM (\index -> generateName "In" ("_" ++ show index) typeName) [1 .. arity]
    return (typeName, inQualids)

  generateInProperties :: Map.Map IR.QName [Coq.Qualid] -> IR.TypeDecl -> Converter [Coq.IndBody]
  generateInProperties _ (IR.TypeSynDecl _ _ _ _) = error "generateInProperty: Type synonym not allowed"
  generateInProperties inQualidMap (IR.DataDecl _ (IR.DeclIdent _ typeName) typeVarDecls conDecls) =
    mapM (generateInProperty inQualidMap typeName typeVarDecls conDecls) [0 .. length typeVarDecls - 1]

  generateInProperty :: Map.Map IR.QName [Coq.Qualid] -> IR.QName -> [IR.TypeVarDecl] -> [IR.ConDecl] -> Int -> Converter Coq.IndBody
  generateInProperty inQualidMap typeName typeVarDecls conDecls index = do
    Just typeQualid <- inEnv $ lookupIdent IR.TypeScope typeName
    let inQualid = (inQualidMap Map.! typeName) !! index
    (cons, mkBody) <- localEnv $ do
      (typeVarQualids, typeVarBinders) <- convertTypeVarDecls' Coq.Explicit typeVarDecls
      let binders = genericArgDecls Coq.Explicit ++ typeVarBinders
          returnType = Coq.Arrow (Coq.Qualid $ typeVarQualids !! index)
                         (Coq.Arrow (genericApply typeQualid [] [] (map Coq.Qualid typeVarQualids))
                           (Coq.Sort Coq.Prop))
          mkBody cons' = Coq.IndBody inQualid binders returnType cons'
      cons <- concatMapM (generateInConstructors typeVarQualids) conDecls
      return (cons, mkBody)
    cons' <- mapM (\(conName, mbConType) -> (\conQualid -> (conQualid, [], mbConType)) <$> generateConName inQualid conName) cons
    return $ mkBody cons'
   where
    generateInConstructors :: [Coq.Qualid] -> IR.ConDecl -> Converter [(IR.QName, Maybe Coq.Term)]
    generateInConstructors typeVarQualids (IR.ConDecl _ (IR.DeclIdent _ conName) args) = localEnv $ do
      Just conQualid <- inEnv $ lookupIdent IR.ValueScope conName
      (argQualids, argBinders) <- unzip <$> mapM (convertAnonymousArg . Just) args
      elemQualid <- freshCoqQualid "x"
      occurrences <- concatMapM (uncurry $ findOccurrences elemQualid) $ zip argQualids args
      let inQualid = (inQualidMap Map.! typeName) !! index
          inResult = genericApply inQualid [] []
            (   map Coq.Qualid typeVarQualids
             ++ [Coq.Qualid elemQualid]
             ++ [genericApply conQualid [] (map Coq.Qualid typeVarQualids) (map Coq.Qualid argQualids)])
          elemBinder = Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit elemQualid (Coq.Qualid elemType)
          mkConType (occBinders, inHypotheses) = Coq.forall
            (elemBinder : occBinders ++ argBinders)
            (foldr Coq.Arrow inResult (reverse inHypotheses))
          conTypes = map mkConType occurrences
      return $ map ((,) conName . Just) conTypes
     where
      elemType :: Coq.Qualid
      elemType = typeVarQualids !! index

      inHypothesis :: Coq.Qualid -> [Coq.Term] -> Coq.Qualid -> Coq.Qualid -> Coq.Term
      inHypothesis inQualid typeArgs containerQualid elemQualid =
        genericApply inQualid [] [] (typeArgs ++ [Coq.Qualid elemQualid, Coq.Qualid containerQualid])

      findOccurrences :: Coq.Qualid -> Coq.Qualid -> IR.Type -> Converter [([Coq.Binder], [Coq.Term])]
      findOccurrences elemQualid argQualid argType = do
        coqType  <- convertType' argType
        argType' <- expandAllTypeSynonyms argType
        findOccurrences_1 elemQualid (inHypothesis Coq.Base.inFree [coqType] argQualid) argType'
        
      findOccurrences_1 :: Coq.Qualid -> (Coq.Qualid -> Coq.Term) -> IR.Type -> Converter [([Coq.Binder], [Coq.Term])]
      findOccurrences_1 _ _ (IR.FuncType _ _ _) = return []
      findOccurrences_1 _ _ (IR.TypeCon _ _)    = return [] -- Ignore type constructors that do not have any type variable or are partially applied
      findOccurrences_1 elemQualid mkInHyp tvar@(IR.TypeVar _ _) = do
        tvarType <- convertType' tvar
        return [([], [mkInHyp elemQualid]) | tvarType == Coq.Qualid elemType]
      findOccurrences_1 elemQualid mkInHyp fullType@(IR.TypeApp _ _ _) =
        findOccurrences_2 fullType []
       where
        findOccurrences_2 :: IR.Type -> [IR.Type] -> Converter [([Coq.Binder], [Coq.Term])]
        findOccurrences_2 (IR.FuncType _ _ _) _ = return []
        findOccurrences_2 (IR.TypeApp _ tcon lastArg) typeArgs = findOccurrences_2 tcon (lastArg : typeArgs)
        findOccurrences_2 (IR.TypeVar _ _) _ = return []
        findOccurrences_2 (IR.TypeCon _ tconName) typeArgs = localEnv $ do
          Just tconArity <- inEnv $ lookupArity IR.TypeScope tconName
          if tconArity == length typeArgs
            then do
              coqArgs <- mapM convertType' typeArgs
              inTypes <- getInTypes inQualidMap tconName
              (containerQualid, containerBinder) <- convertAnonymousArg' (Just fullType)
              occurrences <- concatMapM (\(it,arg) -> findOccurrences_1 elemQualid (inHypothesis it coqArgs containerQualid) arg) $ zip inTypes typeArgs
              let mkNewOcc (occBinders, inHypotheses) = (containerBinder : (reverse occBinders), mkInHyp containerQualid : inHypotheses)
              return $ map mkNewOcc occurrences
            else return []

  -----------------------------------------------------------------------------
  -- Induction Schemes                                                       --
  -----------------------------------------------------------------------------

  -- | Generates an induction scheme for the data type.
  generateSchemeLemma :: Map.Map IR.QName Coq.Qualid -> Map.Map IR.QName Coq.Qualid -> IR.TypeDecl -> Converter (Coq.Qualid, [Coq.Binder], Coq.Term, Coq.Proof)
  generateSchemeLemma _ _ (IR.TypeSynDecl _ _ _ _) = error "generateInductionLemma: Type synonym not allowed"
  generateSchemeLemma schemeQualidMap forQualidMap (IR.DataDecl _ (IR.DeclIdent _ typeName) typeVarDecls conDecls) = localEnv $ do
    Just typeQualid <- inEnv $ lookupIdent IR.TypeScope typeName
    (tvarQualids, tvarBinders) <- convertTypeVarDecls' Coq.Explicit typeVarDecls
    (propQualid, propBinder) <- generateArg "P"
      (Coq.Arrow (genericApply typeQualid [] [] (map Coq.Qualid tvarQualids))
       (Coq.Sort Coq.Prop))
    indCases <- mapM (generateInductionCase propQualid) conDecls
    (valIdent, valBinder) <- generateArg freshArgPrefix
      (genericApply typeQualid [] [] (map Coq.Qualid tvarQualids))
    (indCaseQualids, fixpointQualid, varQualid) <- localEnv $
      do indCaseQualids <- mapM (const $ freshCoqQualid "InductionCase") indCases
         fixpointQualid <- freshCoqQualid "FP"
         varQualid <- freshCoqQualid "x"
         return (indCaseQualids, fixpointQualid, varQualid)
    let schemeName = schemeQualidMap Map.! typeName
        binders = genericArgDecls Coq.Explicit
          ++ tvarBinders
          ++ [propBinder]
        goal    = Coq.forall [valBinder]
          (Coq.app (Coq.Qualid propQualid) [Coq.Qualid valIdent])
        term    = Coq.forall binders (foldr Coq.Arrow goal indCases)
        vars    = map (fromJust . Coq.unpackQualid) (Coq.Base.shape : Coq.Base.pos : tvarQualids ++ [propQualid] ++ indCaseQualids)
        fixpoint = fromJust $ Coq.unpackQualid fixpointQualid
        var = fromJust $ Coq.unpackQualid varQualid
        proof   = Coq.ProofQed
                 (Text.pack
                  $  "  intros" ++ concatMap (\v -> ' ' : v) vars ++ ";\n"
                  ++ "  fix " ++ fixpoint ++ " 1; intro " ++ var ++ "; "
                  ++ fromJust (Coq.unpackQualid Coq.Base.proveInd)
                  ++ ".")
    return (schemeName, [], term, proof)
   where
    -- | Generates an induction case for a given property and constructor.
    generateInductionCase
      :: Coq.Qualid -> IR.ConDecl -> Converter Coq.Term
    generateInductionCase propQualid (IR.ConDecl _ (IR.DeclIdent _ conName) argTypes) = localEnv $ do
      Just conQualid <- inEnv $ lookupIdent IR.ValueScope conName
      argTypes' <- mapM expandAllTypeSynonyms argTypes
      Just conType <- inEnv $ lookupReturnType IR.ValueScope conName
      conType' <- convertType' conType
      (argQualids, argBinders) <- mapAndUnzipM convertAnonymousArg (map Just argTypes)
      hypotheses <- catMaybes <$> mapM (uncurry $ generateInductionHypothesis propQualid conType') (zip argQualids argTypes')
      -- Create induction case.
      let term = foldr Coq.Arrow (Coq.app (Coq.Qualid propQualid) [Coq.app (Coq.Qualid conQualid) (map Coq.Qualid argQualids)]) hypotheses
          indCase = Coq.forall argBinders term
      return indCase

    generateInductionHypothesis :: Coq.Qualid -> Coq.Term -> Coq.Qualid -> IR.Type -> Converter (Maybe Coq.Term)
    generateInductionHypothesis propQualid conType argQualid argType = do
      mbHypothesis <- generateInductionHypothesis_1 argType
      argType' <- convertType' argType
      case mbHypothesis of
        Just hypothesis -> return $ Just $ genericApply Coq.Base.forFree [] [] [argType', hypothesis, Coq.Qualid argQualid]
        Nothing -> return Nothing
     where
      generateInductionHypothesis_1 :: IR.Type -> Converter (Maybe Coq.Term)
      generateInductionHypothesis_1 (IR.FuncType _ _ _) = return Nothing
      generateInductionHypothesis_1 t@(IR.TypeApp _ tcon lastArg) = do
        t' <- convertType' t
        if conType == t'
          then return $ Just $ Coq.Qualid propQualid
          else generateInductionHypothesis_2 tcon [lastArg]
      generateInductionHypothesis_1 t@(IR.TypeCon _ _) = do
        t' <- convertType' t
        if conType == t'
          then return $ Just $ Coq.Qualid propQualid
          else return Nothing -- Ignore type constructors that do not have any type variable or are partially applied
      generateInductionHypothesis_1 (IR.TypeVar _ _) = return Nothing

      generateInductionHypothesis_2 :: IR.Type -> [IR.Type] -> Converter (Maybe Coq.Term)
      generateInductionHypothesis_2 (IR.FuncType _ _ _) _ = return Nothing
      generateInductionHypothesis_2 (IR.TypeApp _ tcon lastArg) typeArgs = generateInductionHypothesis_2 tcon (lastArg : typeArgs)
      generateInductionHypothesis_2 (IR.TypeCon _ tconName) typeArgs = do
        Just tconArity <- inEnv $ lookupArity IR.TypeScope tconName
        hypotheses <- mapM generateInductionHypothesis_1 typeArgs
        if (tconArity == length typeArgs) && (not $ null $ catMaybes hypotheses)
          then do let hypotheses' = map (fromMaybe (Coq.Qualid Coq.Base.noProperty)) hypotheses
                  coqArgs <- mapM convertType' typeArgs
                  forType <- getForType forQualidMap tconName
                  return $ Just $ genericApply forType [] [] (coqArgs ++ hypotheses')
          else return Nothing
      generateInductionHypothesis_2 (IR.TypeVar _ _) _ = return Nothing

  -----------------------------------------------------------------------------
  -- Forall Lemmas                                                           --
  -----------------------------------------------------------------------------

  generateForallLemma :: Map.Map IR.QName Coq.Qualid -> Map.Map IR.QName Coq.Qualid -> Map.Map IR.QName [Coq.Qualid] -> IR.TypeDecl -> Converter (Coq.Qualid, [Coq.Binder], Coq.Term, Coq.Proof)
  generateForallLemma _ _ _ (IR.TypeSynDecl _ _ _ _) = error "generateForallLemma: Type synonym not allowed"
  generateForallLemma forallQualidMap forQualidMap inQualidMap (IR.DataDecl _ (IR.DeclIdent _ typeName) typeVarDecls _) = localEnv $ do
    Just typeQualid <- inEnv $ lookupIdent IR.TypeScope typeName
    (tvarQualids, tvarBinders) <- convertTypeVarDecls' Coq.Explicit typeVarDecls
    (propQualids, propBinders) <- mapAndUnzipM (\tv -> generateArg "P" (Coq.Arrow (Coq.Qualid tv) (Coq.Sort Coq.Prop))) tvarQualids
    (valQualid, valBinder) <- generateArg freshArgPrefix
      (genericApply typeQualid [] [] (map Coq.Qualid tvarQualids))
    inTerms <- mapM (uncurry $ generateInTerm valQualid tvarQualids) $ zip [0 ..] propQualids
    let forallQualid = forallQualidMap Map.! typeName
        forQualid = forQualidMap Map.! typeName
        binders = genericArgDecls Coq.Explicit ++ tvarBinders ++ propBinders ++ [valBinder]
        lhs = genericApply forQualid [] [] (map Coq.Qualid $ tvarQualids ++ propQualids ++ [valQualid])
        rhs = let (inQualids', [lastIn]) = splitAt (length inTerms - 1) $ inTerms
              in  foldr Coq.conj lastIn inQualids'
        term = Coq.forall binders (Coq.equiv lhs rhs)
        proof = Coq.ProofQed $ Text.pack ""
    return (forallQualid, [], term, proof)
   where
    generateInTerm :: Coq.Qualid -> [Coq.Qualid] -> Int -> Coq.Qualid -> Converter Coq.Term
    generateInTerm valQualid tvarQualids index propQualid = localEnv $ do
      let inQualid = (inQualidMap Map.! typeName) !! index
      (val2Qualid, val2Binder) <- generateArg "y" (Coq.Qualid $ tvarQualids !! index)
      let isIn = genericApply inQualid [] [] (map Coq.Qualid $ tvarQualids ++ [val2Qualid, valQualid])
      return $ Coq.forall [val2Binder] $ Coq.Arrow isIn (Coq.app (Coq.Qualid propQualid) [Coq.Qualid val2Qualid])

  -----------------------------------------------------------------------------
  -- Helper Functions                                                        --
  -----------------------------------------------------------------------------

  hasTypeVar :: IR.TypeDecl -> Bool
  hasTypeVar (IR.TypeSynDecl _ _ _ _) = error "hasTypeVar: Type synonym not allowed"
  hasTypeVar (IR.DataDecl _ _ typeVarDecls _) = not $ null typeVarDecls

  generateName :: String -> String -> IR.QName -> Converter (IR.QName, Coq.Qualid)
  generateName prefix suffix typeQName = do
    Just typeQualid <- inEnv $ lookupIdent IR.TypeScope typeQName
    let Just typeIdent = Coq.unpackQualid typeQualid
    newQualid <- freshCoqQualid $ prefix ++ typeIdent ++ suffix
    return (typeQName, newQualid)

  generateConName :: Coq.Qualid -> IR.QName -> Converter Coq.Qualid
  generateConName baseQualid conQName = do
    Just conQualid <- inEnv $ lookupIdent IR.ValueScope conQName
    let Just baseName = Coq.unpackQualid baseQualid
        Just conName    = Coq.unpackQualid conQualid 
    freshCoqQualid $ baseName ++ "_" ++ conName

  getForType :: Map.Map IR.QName Coq.Qualid -> IR.QName -> Converter Coq.Qualid
  getForType forQualidMap t = case forQualidMap Map.!? t of
    Just qualid -> return qualid
    Nothing -> do
      -- TODO use environment to store and load other 'For-' properties
      Just qualid <- inEnv $ lookupIdent IR.TypeScope t
      let name = case qualid of
            Coq.Bare n -> Text.unpack n
            Coq.Qualified _ n -> Text.unpack n
      return $ Coq.bare $ "For" ++ name

  getInTypes :: Map.Map IR.QName [Coq.Qualid] -> IR.QName -> Converter [Coq.Qualid]
  getInTypes inQualidMap t = case inQualidMap Map.!? t of
    Just qualids -> return  qualids
    Nothing -> do
      -- TODO use environment to store and load other 'In-' properties
      Just qualid <- inEnv $ lookupIdent IR.TypeScope t
      Just arity <- inEnv $ lookupArity IR.TypeScope t
      let name = case qualid of
            Coq.Bare n -> Text.unpack n
            Coq.Qualified _ n -> Text.unpack n
          suffixes = if arity == 1
            then [""]
            else map (\index -> "_" ++ show index) [1 .. arity]
      return $ map (\suffix -> Coq.bare $ "In" ++ name ++ suffix) suffixes

  generateArg :: String -> Coq.Term -> Converter (Coq.Qualid, Coq.Binder)
  generateArg argName argType = do
    qualid <- freshCoqQualid argName
    let binder = Coq.typedBinder Coq.Ungeneralizable Coq.Explicit [qualid] argType
    return (qualid, binder)
