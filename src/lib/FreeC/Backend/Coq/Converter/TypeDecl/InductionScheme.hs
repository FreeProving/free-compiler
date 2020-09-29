-- This module defines and proofs induction schemes for data declarations.
-- It also creates helper types and lemmas for those induction schemes.
module FreeC.Backend.Coq.Converter.TypeDecl.InductionScheme where

import           Control.Monad                    ( mapAndUnzipM )
import           Control.Monad.Extra              ( concatMapM )
import           Data.List                        ( nub, intercalate ) 
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
  ( freshArgPrefix, freshCoqQualid, freshCoqIdent )
import           FreeC.Environment.LookupOrFail (lookupIdentOrFail)
import qualified FreeC.IR.Syntax                  as IR
import           FreeC.IR.TypeSynExpansion
import           FreeC.Monad.Converter
import           FreeC.Pretty

type LookupMap a = Map.Map IR.QName a

-- | Creates induction schemes and helpers for a list of data declarations.
generateInductionSchemes :: [IR.TypeDecl] -> Converter [Coq.Sentence]
generateInductionSchemes dataDecls = do
  -- Filter the data declarations that need helpers.
  let complexDataDecls = filter hasTypeVar dataDecls
  -- Generate names.
  forQualidMap <- Map.fromList <$> mapM (generateName "For" "" . IR.typeDeclQName) complexDataDecls
  inQualidMap <- Map.fromList <$> mapM (generateInNames . IR.typeDeclQName) complexDataDecls
  schemeQualidMap <- Map.fromList <$> mapM (generateName "" "_ind" . IR.typeDeclQName) dataDecls
  forallQualidMap <- Map.fromList <$> mapM (generateName "For" "_forall". IR.typeDeclQName) complexDataDecls
  -- Generate properties.
  forBodies <- mapM (generateForProperty forQualidMap) complexDataDecls
  (inBodies', inConNames) <- mapAndUnzipM (generateInProperties inQualidMap) complexDataDecls
  let inBodies = concat inBodies'
  -- Generate induction schemes.
  schemeBodies <- mapM (generateSchemeLemma schemeQualidMap forQualidMap) dataDecls
  -- Generate lemmas and hints.
  forallBodies <- mapM (uncurry $ generateForallLemma schemeQualidMap forallQualidMap forQualidMap inQualidMap) $ zip inConNames complexDataDecls
  hintSentences <- concatMapM (generateHints schemeQualidMap forallQualidMap forQualidMap inQualidMap) complexDataDecls
  -- Insert names into environment.
  mapM_ (insertPropertiesInEnv forQualidMap inQualidMap forallQualidMap . IR.typeDeclQName) complexDataDecls 
  -- Return result
  return
    ( Coq.commentedSentences ("ForType properties for " ++ showPretty (map IR.typeDeclName dataDecls))
      [Coq.InductiveSentence (Coq.Inductive (NonEmpty.fromList forBodies) []) | not (null forBodies)]
    ++ Coq.commentedSentences ("InType properties for " ++ showPretty (map IR.typeDeclName dataDecls))
       [Coq.InductiveSentence (Coq.Inductive (NonEmpty.fromList inBodies) []) | not (null inBodies)]
    ++ Coq.commentedSentences ("Induction schemes for " ++ showPretty (map IR.typeDeclName dataDecls))
       (map (\(name, binders, term, proof) ->
              Coq.AssertionSentence (Coq.Assertion Coq.Lemma name binders term) proof) schemeBodies)
    ++ Coq.commentedSentences ("Forall lemmas for " ++ showPretty (map IR.typeDeclName dataDecls))
       (map (\(name, binders, term, proof) ->
              Coq.AssertionSentence (Coq.Assertion Coq.Lemma name binders term) proof) forallBodies)
    ++ Coq.commentedSentences "Give hints"
       hintSentences
    )
 where
  -----------------------------------------------------------------------------
  -- @ForType@ Properties                                                    --
  -----------------------------------------------------------------------------

  -- | Generates the 'For-' property for a given data declaration.
  --   If the data declaration has @n@ type variables @a1 ... an@ then the property
  --   will be of the form:
  --   > ForType Shape Pos a_1 ... a_n P_1 ... P_n x
  --   This property states that for every @1 <= i <= n@ and every element @y@ of
  --   type @a_i@ which is contained in @x@, the property @P_i y@ holds.
  generateForProperty :: LookupMap Coq.Qualid -> IR.TypeDecl -> Converter Coq.IndBody
  generateForProperty _ (IR.TypeSynDecl _ _ _ _) = error "generateForProperty: Type synonym not allowed"
  generateForProperty forQualidMap (IR.DataDecl _ (IR.DeclIdent srcSpan typeName) typeVarDecls conDecls) = do
    -- Generate constructor names.
    forConQualids <- mapM (generateConName forQualid . IR.conDeclQName) conDecls
    -- Enter local environment.
    localEnv $ do
      -- Collect and generate relevant Coq names.
      typeQualid <- lookupIdentOrFail srcSpan IR.TypeScope typeName
      (typeVarQualids, typeVarBinders) <- convertTypeVarDecls' Coq.Explicit typeVarDecls
      propertyQualids <- mapM  (const $ freshCoqQualid "P") typeVarQualids
      -- Generate constructors for the 'For-' property.
      forCons <- mapM (uncurry (generateForConstructor typeVarQualids propertyQualids)) $ zip conDecls forConQualids
      -- Stick everything together.
      let propertyTypes = map  (\a -> (Coq.Arrow (Coq.Qualid a) (Coq.Sort Coq.Prop))) typeVarQualids
          propertyBinders = map (\(a,t) -> Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit a t) $ zip propertyQualids propertyTypes
          binders = genericArgDecls Coq.Explicit ++ typeVarBinders ++ propertyBinders
          returnType = Coq.Arrow (genericApply typeQualid [] [] (map Coq.Qualid typeVarQualids))
                             (Coq.Sort Coq.Prop)
      return $ Coq.IndBody forQualid binders returnType forCons
   where
    -- | The name of the 'For-' property which we are generating.
    forQualid :: Coq.Qualid
    forQualid = forQualidMap Map.! typeName

    -- | Generates a constructor for the 'For-' property.
    generateForConstructor :: [Coq.Qualid] -> [Coq.Qualid] -> IR.ConDecl -> Coq.Qualid -> Converter (Coq.Qualid, [Coq.Binder], Maybe Coq.Term)
    generateForConstructor typeVarQualids propertyQualids (IR.ConDecl _ (IR.DeclIdent srcSpan' conName) args) forConQualid = localEnv $ do
      -- Collect and generate relevant Coq names.
      conQualid <- lookupIdentOrFail srcSpan' IR.ValueScope conName
      (argQualids, binders) <- unzip <$> mapM (convertAnonymousArg . Just) args
      -- Generate a hypothesis for every argument of the constructor.
      -- But ignore trivial hypotheses.
      forHypotheses <- catMaybes <$> (mapM (uncurry generateForHypothesis) $ zip argQualids args)
      -- Generate constructor.
      let forResult = genericApply forQualid [] []
            (   map Coq.Qualid typeVarQualids
             ++ map Coq.Qualid propertyQualids
             ++ [genericApply conQualid [] (map Coq.Qualid typeVarQualids) (map Coq.Qualid argQualids)])
          returnType = Coq.forall binders (foldr Coq.Arrow forResult forHypotheses)
      return (forConQualid, [], Just returnType)
     where
      propertyMap :: Map.Map Coq.Qualid Coq.Qualid
      propertyMap = Map.fromList $ zip typeVarQualids propertyQualids

      -- | Generates an hypothesis for an argument of a 'For-' constructor.
      generateForHypothesis :: Coq.Qualid -> IR.Type -> Converter (Maybe Coq.Term)
      generateForHypothesis argQualid argType = do
        -- Expand type synonyms in the argument type and search for occurrences of the type variables.
        coqType  <- convertType' argType
        argType' <- expandAllTypeSynonyms argType
        mbHyp <- generateForHypothesis_1 0 argType'
        -- Wrap generated hypothesis in a @ForFree@ property and apply it to the argument.
        return $ case mbHyp of
          Just hyp -> Just $ genericApply Coq.Base.forFree [] [] [coqType, hyp, Coq.Qualid argQualid]
          Nothing  -> Nothing

      -- | Generates an hypothesis for a by searching in the given IR type.
      --   Memorizes the depth of the current search path.
      generateForHypothesis_1 :: Int -> IR.Type -> Converter (Maybe Coq.Term)
      generateForHypothesis_1 _ (IR.FuncType _ _ _) =
        -- Ignore functions.
        return Nothing
      generateForHypothesis_1 d (IR.TypeApp _ tcon lastArg) =
        -- Unfold the type application.
        generateForHypothesis_2 d tcon [lastArg]
      generateForHypothesis_1 _ (IR.TypeCon _ _)    =
        -- Ignore type constructors that do not have any type variable or are partially applied.
        return Nothing
      generateForHypothesis_1 _ tvar@(IR.TypeVar _ _) = do
        -- Lookup hypothesis that has to hold for the given type variable.
        Coq.Qualid tvarQualid <- convertType' tvar
        return $ Coq.Qualid <$> propertyMap Map.!? tvarQualid

      -- | Unfolds a type application
      --   Memorizes the depth of the current search path.
      generateForHypothesis_2 :: Int -> IR.Type -> [IR.Type] -> Converter (Maybe Coq.Term)
      generateForHypothesis_2 _ (IR.FuncType _ _ _) _ =
        -- Ignore functions.
        return Nothing
      generateForHypothesis_2 d (IR.TypeApp _ tcon lastArg) typeArgs =
        -- Continue unfolding.
        generateForHypothesis_2 d tcon (lastArg : typeArgs)
      generateForHypothesis_2 d (IR.TypeCon _ tconName) typeArgs = do
        -- Recursively generate hypotheses for type arguments.
        hypotheses <- mapM (generateForHypothesis_1 (d+1)) typeArgs
        -- Only consider fully applied type constructors and only generate a
        -- complex hypothesis, if any of the hypotheses for the arguments is
        -- non trivial.
        Just tconArity <- inEnv $ lookupArity IR.TypeScope tconName
        if (tconArity == length typeArgs) && (not $ null $ catMaybes hypotheses)
          then do
            let hypotheses' = map (fromMaybe (Coq.Qualid Coq.Base.noProperty)) hypotheses
            coqArgs <- mapM convertType' typeArgs
            -- Prevent mutual recursion in the hypotheses and prevent
            -- direct recursion which is deeper than @maxDepth@.
            mbForType <- if tconName == typeName && all (\(tvar, targ) -> Coq.Qualid tvar == targ) (zip typeVarQualids coqArgs) && d <= maxDepth
              then
                -- Legal recursion. 
                return $ Just forQualid
              else
                -- Use already defined 'For-' property
                inEnv $ lookupForProperty tconName
            -- Wrap generated hypotheses in a 'For-' property.
            return ((\forType -> genericApply forType [] [] (coqArgs ++ hypotheses')) <$> mbForType)
          else return Nothing
      generateForHypothesis_2 _ (IR.TypeVar _ _) _ =
        -- Ignore type variables that are used as type constructors.
        return Nothing

  -----------------------------------------------------------------------------
  -- @InType@ Properties                                                     --
  -----------------------------------------------------------------------------

  -- | Generate a name for a 'In-' property for each type variable of the given
  --   type constructor.
  generateInNames :: IR.QName -> Converter (IR.QName, [Coq.Qualid])
  generateInNames typeName = do
    Just arity <- inEnv $ lookupArity IR.TypeScope typeName
    inQualids <- map snd <$>  if arity == 1
      then mapM (generateName "In" "") [typeName]
      else mapM (\index -> generateName "In" ("_" ++ show index) typeName) [1 .. arity]
    return (typeName, inQualids)

  -- | Generates the 'In-' properties for a given data declaration.
  generateInProperties :: LookupMap [Coq.Qualid] -> IR.TypeDecl -> Converter ([Coq.IndBody], [Coq.Qualid])
  generateInProperties _ (IR.TypeSynDecl _ _ _ _) = error "generateInProperty: Type synonym not allowed"
  generateInProperties inQualidMap (IR.DataDecl _ (IR.DeclIdent _ typeName) typeVarDecls conDecls) = do
    (bodies, inConNames) <- mapAndUnzipM (generateInProperty inQualidMap typeName typeVarDecls conDecls) [0 .. length typeVarDecls - 1]
    return (bodies, concat inConNames)

  -- | Generates an 'In-' property for a given data declaration and the type
  --   variable number @index@ of that type and returns the names of its
  --   constructors.
  --   If the data declaration has @n@ type variables @a1 ... an@ then the
  --   property will be of the form:
  --   > InType Shape Pos a_1 ... a_n y x
  --   This property states that the element @y@ of type @a_index@ is contained
  --   in @x@.
  generateInProperty :: LookupMap [Coq.Qualid] -> IR.QName -> [IR.TypeVarDecl] -> [IR.ConDecl] -> Int -> Converter (Coq.IndBody, [Coq.Qualid])
  generateInProperty inQualidMap typeName typeVarDecls conDecls index = do
    -- In contrast to the generation of the 'For-' properties the number of
    -- constructors for a 'In-' property is not known yet.
    -- Therefore we retrieve components from the local environment and connect
    -- them outside of the local environment where we can add the required
    -- environment entries.
    (cons, mkBody) <- localEnv $ do
      -- Collect and generate relevant Coq names.
      Just typeQualid <- inEnv $ lookupIdent IR.TypeScope typeName
      (typeVarQualids, typeVarBinders) <- convertTypeVarDecls' Coq.Explicit typeVarDecls
      -- Generate constructors for the 'In-' property.
      cons <- concatMapM (generateInConstructors typeVarQualids) conDecls
      -- Start sticking everything together.
      let binders = genericArgDecls Coq.Explicit ++ typeVarBinders
          returnType = Coq.Arrow (Coq.Qualid $ typeVarQualids !! index)
                         (Coq.Arrow (genericApply typeQualid [] [] (map Coq.Qualid typeVarQualids))
                           (Coq.Sort Coq.Prop))
          mkBody = Coq.IndBody inQualid binders returnType
      return (cons, mkBody)
    -- Generate constructor names and add empty binding list.
    inConNames <- mapM (generateConName inQualid . fst) cons
    let cons' = map (\(inConName, mbConType) -> (inConName, [], mbConType)) $
          zip inConNames $ map snd cons
    return (mkBody cons', inConNames)
   where
    -- | The name of the 'In-' property which we are generating.
    inQualid :: Coq.Qualid
    inQualid = (inQualidMap Map.! typeName) !! index
    
    -- | Generates constructors for the 'In-' property.
    generateInConstructors :: [Coq.Qualid] -> IR.ConDecl -> Converter [(IR.QName, Maybe Coq.Term)]
    generateInConstructors typeVarQualids (IR.ConDecl _ (IR.DeclIdent srcSpan conName) args) = localEnv $ do
      -- Collect and generate relevant Coq names.
      conQualid <- lookupIdentOrFail srcSpan IR.ValueScope conName
      (argQualids, argBinders) <- unzip <$> mapM (convertAnonymousArg . Just) args
      elemQualid <- freshCoqQualid "x"
      -- Find occurrences of the relevant type variable in the arguments.
      occurrences <- concatMapM (uncurry $ findOccurrences elemQualid) $ zip argQualids args
      -- Generate a constructor for each occurrence.
      let inResult = genericApply inQualid [] []
            (   map Coq.Qualid typeVarQualids
             ++ [Coq.Qualid elemQualid]
             ++ [genericApply conQualid [] (map Coq.Qualid typeVarQualids) (map Coq.Qualid argQualids)])
          elemBinder = Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit elemQualid elemType
          mkConType (occBinders, inHypotheses) = Coq.forall
            (elemBinder : occBinders ++ argBinders)
            (foldr Coq.Arrow inResult (reverse inHypotheses))
          conTypes = map mkConType occurrences
      return $ map ((,) conName . Just) conTypes
     where
      -- | The type variable we are looking for.
      elemType :: Coq.Term
      elemType = Coq.Qualid (typeVarQualids !! index)

      -- | Smart constructor for an 'In-' property.
      inHypothesis :: Coq.Qualid -> [Coq.Term] -> Coq.Qualid -> Coq.Qualid -> Coq.Term
      inHypothesis inQualid' typeArgs containerQualid elemQualid =
        genericApply inQualid' [] [] (typeArgs ++ [Coq.Qualid elemQualid, Coq.Qualid containerQualid])

      -- | Find occurrences of the relevant type variable in the given type.
      findOccurrences :: Coq.Qualid -> Coq.Qualid -> IR.Type -> Converter [([Coq.Binder], [Coq.Term])]
      findOccurrences elemQualid argQualid argType = do
        -- Expand type synonyms in the argument type and search for occurrences of the type variable.
        coqType  <- convertType' argType
        argType' <- expandAllTypeSynonyms argType
        findOccurrences_1 0 elemQualid (inHypothesis Coq.Base.inFree [coqType] argQualid) argType'
 
      -- | Find occurrences of the relevant type variable in the given type.
      --   Memorizes the depth of the current search path.
      findOccurrences_1 :: Int -> Coq.Qualid -> (Coq.Qualid -> Coq.Term) -> IR.Type -> Converter [([Coq.Binder], [Coq.Term])]
      findOccurrences_1 _ _ _ (IR.FuncType _ _ _) =
        -- Ignore functions.
        return []
      findOccurrences_1 _ _ _ (IR.TypeCon _ _)    =
        -- Ignore type constructors that do not have any type variable or are partially applied
        return []
      findOccurrences_1 _ elemQualid mkInHyp tvar@(IR.TypeVar _ _) = do
        -- If this is the desired type variable, return an occurrence.
        tvarType <- convertType' tvar
        return [([], [mkInHyp elemQualid]) | tvarType == elemType]
      findOccurrences_1 d elemQualid mkInHyp fullType@(IR.TypeApp _ _ _) =
        -- Unfold type application.
        findOccurrences_2 fullType []
       where
        -- | Unfolds a type application.
        findOccurrences_2 :: IR.Type -> [IR.Type] -> Converter [([Coq.Binder], [Coq.Term])]
        findOccurrences_2 (IR.FuncType _ _ _) _ =
          -- Ignore functions.
          return []
        findOccurrences_2 (IR.TypeApp _ tcon lastArg) typeArgs =
          -- Continue unfolding.
          findOccurrences_2 tcon (lastArg : typeArgs)
        findOccurrences_2 (IR.TypeVar _ _) _ =
          -- Ignore type variables that are used as type constructors.
          return []
        findOccurrences_2 (IR.TypeCon _ tconName) typeArgs = localEnv $ do
          -- Only consider fully applied type constructors.
          Just tconArity <- inEnv $ lookupArity IR.TypeScope tconName
          if tconArity == length typeArgs
            then do
              coqArgs <- mapM convertType' typeArgs
              -- Prevent mutual recursion in the hypotheses and prevent
              -- direct recursion which is deeper than @maxDepth@.
              mbInTypes <- if tconName == typeName && all (\(tvar, targ) -> Coq.Qualid tvar == targ) (zip typeVarQualids coqArgs) && d <= maxDepth
                then
                  -- Legal recursion.
                  return $ inQualidMap Map.!? tconName
                else 
                  -- Use already defined 'In-' properties
                  inEnv $ lookupInProperties tconName
              case mbInTypes of
                Just inTypes -> do
                  -- Generate intermediate container and recursively search in type arguments.
                  (containerQualid, containerBinder) <- convertAnonymousArg' (Just fullType)
                  occurrences <- concatMapM (\(it,arg) -> findOccurrences_1 (d+1) elemQualid (inHypothesis it coqArgs containerQualid) arg) $ zip inTypes typeArgs
                  let mkNewOcc (occBinders, inHypotheses) = (containerBinder : (reverse occBinders), mkInHyp containerQualid : inHypotheses)
                  return $ map mkNewOcc occurrences
                Nothing -> return []
            else return []

  -----------------------------------------------------------------------------
  -- Induction Schemes                                                       --
  -----------------------------------------------------------------------------

  -- | Generates an induction scheme for the give data type declaration.
  generateSchemeLemma :: LookupMap Coq.Qualid -> LookupMap Coq.Qualid -> IR.TypeDecl -> Converter (Coq.Qualid, [Coq.Binder], Coq.Term, Coq.Proof)
  generateSchemeLemma _ _ (IR.TypeSynDecl _ _ _ _) = error "generateInductionLemma: Type synonym not allowed"
  generateSchemeLemma schemeQualidMap forQualidMap (IR.DataDecl _ (IR.DeclIdent srcSpan typeName) typeVarDecls conDecls) = localEnv $ do
    -- Collect and generate relevant Coq names.
    typeQualid <- lookupIdentOrFail srcSpan IR.TypeScope typeName
    (tvarQualids, tvarBinders) <- convertTypeVarDecls' Coq.Explicit typeVarDecls
    (propQualid, propBinder) <- generateArg "P"
      (Coq.Arrow (genericApply typeQualid [] [] (map Coq.Qualid tvarQualids))
       (Coq.Sort Coq.Prop))
    -- Generate induction cases for constructors.
    indCases <- mapM (generateInductionCase propQualid) conDecls
    -- Generate lemma.
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
        -- Generate proof.
        vars    = map (fromJust . Coq.unpackQualid) (Coq.Base.shape : Coq.Base.pos : tvarQualids ++ [propQualid] ++ indCaseQualids)
        fixpoint = fromJust $ Coq.unpackQualid fixpointQualid
        var = fromJust $ Coq.unpackQualid varQualid
        proof   = Coq.ProofDefined
                 (Text.pack
                  $  "  intros" ++ concatMap (\v -> ' ' : v) vars ++ ";\n"
                  ++ "  fix " ++ fixpoint ++ " 1; intro " ++ var ++ ";\n"
                  ++ "  " ++ Text.unpack Coq.Base.proveInd
                  ++ ".")
    return (schemeName, [], term, proof)
   where
    -- | Generates an induction case for a given property and constructor.
    generateInductionCase
      :: Coq.Qualid -> IR.ConDecl -> Converter Coq.Term
    generateInductionCase propQualid (IR.ConDecl _ (IR.DeclIdent srcSpan' conName) argTypes) = localEnv $ do
      -- Collect and generate relevant Coq names.
      conQualid <- lookupIdentOrFail srcSpan' IR.ValueScope conName
      (argQualids, argBinders) <- mapAndUnzipM convertAnonymousArg (map Just argTypes)
      -- Expand type synonyms in the argument types and create induction hypotheses.
      argTypes' <- mapM expandAllTypeSynonyms argTypes
      Just conType <- inEnv $ lookupReturnType IR.ValueScope conName
      conType' <- convertType' conType
      hypotheses <- catMaybes <$> mapM (uncurry $ generateInductionHypothesis propQualid conType') (zip argQualids argTypes')
      -- Generate induction case.
      let term = foldr Coq.Arrow (Coq.app (Coq.Qualid propQualid) [Coq.app (Coq.Qualid conQualid) (map Coq.Qualid argQualids)]) hypotheses
          indCase = Coq.forall argBinders term
      return indCase

    -- | Generates an induction hypothesis for a given property and constructor argument.
    generateInductionHypothesis :: Coq.Qualid -> Coq.Term -> Coq.Qualid -> IR.Type -> Converter (Maybe Coq.Term)
    generateInductionHypothesis propQualid conType argQualid argType = do
      -- Generate induction hypotheses with a maximal depth of @maxDepth@.
      mbHypothesis <- generateInductionHypothesis_1 maxDepth argType
        -- Wrap generated hypothesis in a @ForFree@ property and apply it to the argument.
      argType' <- convertType' argType
      case mbHypothesis of
        Just hypothesis -> return $ Just $ genericApply Coq.Base.forFree [] [] [argType', hypothesis, Coq.Qualid argQualid]
        Nothing -> return Nothing
     where
      -- | Generates an induction hypothesis by searching in the given type for recursive occurrences.
      --   Has an argument limiting the search depth.
      generateInductionHypothesis_1 :: Int -> IR.Type -> Converter (Maybe Coq.Term)
      generateInductionHypothesis_1 _ (IR.FuncType _ _ _) =
        -- Ignore functions.
        return Nothing
      generateInductionHypothesis_1 md t@(IR.TypeApp _ tcon lastArg) = do
        -- Check whether we found a recursive occurrence.
        t' <- convertType' t
        if conType == t'
          then
            return $ Just $ Coq.Qualid propQualid
          else
            -- If we do not have an recursive occurrence and did not reach the
            -- search limit yet, unfold type application.
            if md > 0 then generateInductionHypothesis_2 (md-1) tcon [lastArg] else return Nothing
      generateInductionHypothesis_1 _ t@(IR.TypeCon _ _) = do
        -- Check whether we found a recursive occurrence.
        t' <- convertType' t
        if conType == t'
          then return $ Just $ Coq.Qualid propQualid
          else
            -- Ignore type constructors that do not have any type variable or are partially applied.
            return Nothing
      generateInductionHypothesis_1 _ (IR.TypeVar _ _) =
        -- There is no induction hypothesis for type variables.
        return Nothing

      -- Unfolds a type application.
      generateInductionHypothesis_2 :: Int -> IR.Type -> [IR.Type] -> Converter (Maybe Coq.Term)
      generateInductionHypothesis_2 _ (IR.FuncType _ _ _) _ =
        -- Ignore functions.
        return Nothing
      generateInductionHypothesis_2 md (IR.TypeApp _ tcon lastArg) typeArgs =
        -- Continue unfolding.
        generateInductionHypothesis_2 md tcon (lastArg : typeArgs)
      generateInductionHypothesis_2 md (IR.TypeCon _ tconName) typeArgs = do
        -- Recursively generate hypotheses for type arguments.
        hypotheses <- mapM (generateInductionHypothesis_1 md) typeArgs
        -- Only consider fully applied type constructors and only generate a
        -- complex hypothesis, if any of the hypotheses for the arguments is
        -- non trivial.
        Just tconArity <- inEnv $ lookupArity IR.TypeScope tconName
        if (tconArity == length typeArgs) && (not $ null $ catMaybes hypotheses)
          then do
            let hypotheses' = map (fromMaybe (Coq.Qualid Coq.Base.noProperty)) hypotheses
            coqArgs <- mapM convertType' typeArgs
            mbForType <- getForType forQualidMap tconName
            -- Wrap generated hypotheses in a 'For-' property.
            return ((\forType -> genericApply forType [] [] (coqArgs ++ hypotheses')) <$> mbForType)
          else return Nothing
      generateInductionHypothesis_2 _ (IR.TypeVar _ _) _ =
        -- Ignore type variables that are used as type constructors.
        return Nothing

  -----------------------------------------------------------------------------
  -- Forall Lemmas                                                           --
  -----------------------------------------------------------------------------

  -- | Generates a lemma which states the relation between the 'For-' property
  --   and the 'In-' properties for a data declaration with type variables.
  generateForallLemma :: LookupMap Coq.Qualid -> LookupMap Coq.Qualid ->
    LookupMap Coq.Qualid -> LookupMap [Coq.Qualid] ->
    [Coq.Qualid] -> IR.TypeDecl -> Converter (Coq.Qualid, [Coq.Binder], Coq.Term, Coq.Proof)
  generateForallLemma _ _ _ _ _ (IR.TypeSynDecl _ _ _ _) = error "generateForallLemma: Type synonym not allowed"
  generateForallLemma schemeQualidMap forallQualidMap forQualidMap inQualidMap inConNames (IR.DataDecl _ (IR.DeclIdent _ typeName) typeVarDecls _) = localEnv $ do
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
        vars    = map (fromJust . Coq.unpackQualid) (Coq.Base.shape : Coq.Base.pos : tvarQualids ++ propQualids)
        Just schemeName = Coq.unpackQualid $ schemeQualidMap Map.! typeName
        proof   = Coq.ProofDefined
                 (Text.pack
                  $  concatMap generateForallHint inConNames
                  ++ "  intros" ++ concatMap (\v -> ' ' : v) vars ++ ";\n"
                  ++ "  " ++ Text.unpack Coq.Base.proveForall ++ ' ': schemeName
                  ++ ".")
    return (forallQualid, [], term, proof)
   where
    -- | Generates a term stating that for all elements @y@ of type @a_index@
    --   that are contained in @valQualid@, the property @propQualid y@ holds.
    generateInTerm :: Coq.Qualid -> [Coq.Qualid] -> Int -> Coq.Qualid -> Converter Coq.Term
    generateInTerm valQualid tvarQualids index propQualid = localEnv $ do
      let inQualid = (inQualidMap Map.! typeName) !! index
      (val2Qualid, val2Binder) <- generateArg "y" (Coq.Qualid $ tvarQualids !! index)
      let isIn = genericApply inQualid [] [] (map Coq.Qualid $ tvarQualids ++ [val2Qualid, valQualid])
      return $ Coq.forall [val2Binder] $ Coq.Arrow isIn (Coq.app (Coq.Qualid propQualid) [Coq.Qualid val2Qualid])

    -- | Generate a local hint which is used in the proof of this 'forall' lemma.
    generateForallHint :: Coq.Qualid -> String
    generateForallHint inCon =
      let Just inStr = Coq.unpackQualid inCon
      in  "  Local Hint Extern 1 => " ++ Text.unpack Coq.Base.proveForall_finish ++
          ' ':inStr ++ " : " ++ Text.unpack Coq.Base.proveForall_db ++ ".\n"

  -----------------------------------------------------------------------------
  -- Hints                                                                   --
  -----------------------------------------------------------------------------
  -- | Generates hints that are used in the proofs of induction schemes and
  --   'forall' sentences.
  generateHints :: LookupMap Coq.Qualid -> LookupMap Coq.Qualid -> LookupMap Coq.Qualid -> LookupMap [Coq.Qualid] -> IR.TypeDecl -> Converter [Coq.Sentence]
  generateHints _ _ _ _ (IR.TypeSynDecl _ _ _ _) = error "generateHint: Type synonym not allowed"
  generateHints schemeQualidMap forallQualidMap forQualidMap inQualidMap (IR.DataDecl _ (IR.DeclIdent _ typeName) typeVarDecls tconDecls) = do
    let forall  = forallQualidMap Map.! typeName
        forType = forQualidMap Map.! typeName
        inTypes = inQualidMap Map.! typeName
        scheme  = schemeQualidMap Map.! typeName
    proveIndHint      <- generateProveIndHint typeName forType forall scheme (length typeVarDecls) tconDecls
    proveForallHint1  <- generateProveForallHint1 forType forall (length typeVarDecls)
    proveForallHints2 <- mapM (generateProveForallHint2 forType forall (length typeVarDecls)) inTypes
    return $ [proveIndHint, proveForallHint1] ++ proveForallHints2
  
  -- | Generates a hint for induction scheme generation, using the template
  --   @Coq.Base.proveInd_proveForType@.
  generateProveIndHint :: IR.QName -> Coq.Qualid -> Coq.Qualid -> Coq.Qualid -> Int -> [IR.ConDecl] -> Converter (Coq.Sentence)
  generateProveIndHint typeName forType forall scheme nTvars conDecls = do
    valStr <- localEnv $ freshCoqIdent freshArgPrefix
    dTypes         <- concatMapM getDTypes conDecls
    unfoldSubProps <- nub <$> concatMapM unfoldSubProp dTypes
    let tacticConStr   = Text.unpack Coq.Base.proveInd_proveForType
        Just forallStr = Coq.unpackQualid forall
        Just schemeStr = Coq.unpackQualid scheme
        underscores    = replicate (2 + 2 * nTvars) Coq.UnderscorePat
        valPattern     = Coq.QualidPat $ Coq.bare $ '?':valStr
        forTypePattern = Coq.ArgsPat forType $ underscores ++ [valPattern]
        tactic         = unwords [tacticConStr, valStr, forallStr, schemeStr]
                         ++ (if null unfoldSubProps then "" else (";\nrepeat (\n"
                         ++ tacticUnlines unfoldSubProps
                         ++ ")"))
    return $ Coq.externHint (Just Coq.Global) 0 (Just forTypePattern) tactic [Coq.Base.proveInd_db]
   where
    -- | Tries to simplify a pair of 'For-' and 'In-' hypotheses.
    unfoldSubProp :: IR.QName -> Converter [String]
    unfoldSubProp dname = do
      -- Filter complex data types.
      mbInTs    <- inEnv $ lookupInProperties dname
      case mbInTs of
        Nothing -> return []
        Just inTs -> mapM (unfoldSubProp' dname) inTs

    -- | Tries to simplify a pair of 'For-' and 'In-' hypotheses.
    unfoldSubProp' :: IR.QName -> Coq.Qualid -> Converter String
    unfoldSubProp' dName inT = localEnv $ do
      hForStr      <- freshCoqIdent "HF"
      hInStr       <- freshCoqIdent "HI"
      valStr1      <- freshCoqIdent freshArgPrefix
      valStr2      <- freshCoqIdent freshArgPrefix
      Just forT    <- inEnv $ lookupForProperty dName
      Just forallT <- inEnv $ lookupForallLemma dName
      Just dArity  <- inEnv $ lookupArity IR.TypeScope dName
      let forStr     = unpackQualid' forT
          inStr      = unpackQualid' inT
          forallStr  = unpackQualid' forallT
          forPatStrs = forStr : (replicate (2 + 2 * dArity) "_") ++ ['?':valStr2]
          inPatStrs  = inStr : (replicate (2 + dArity) "_") ++ ['?':valStr1, '?':valStr2]
          tactic          = unlines'
            [ "  try match goal with"
            , "      | [ " ++ hForStr ++ " : " ++ unwords forPatStrs
            , "        , " ++ hInStr ++ " : " ++ unwords inPatStrs
            , "        |- _ ] =>"
            , "          " ++ unwords [Text.unpack Coq.Base.proveInd_ForType_InType, hForStr, hInStr, valStr1, forallStr]
            , "      end"
            ]
      return tactic

    -- | Like @unpackQualid@ but does also return a string for qualified names.
    unpackQualid' :: Coq.Qualid -> String
    unpackQualid' (Coq.Bare n) = Text.unpack n
    unpackQualid' (Coq.Qualified p n) = Text.unpack p ++ "." ++ Text.unpack n

    -- | Like @unlines@, but does not put a line break after the last string.
    unlines' :: [String] -> String
    unlines' = intercalate "\n"

    -- | Like @unlines'@, but inserts also semicolons to connect Coq tactics.
    tacticUnlines :: [String] -> String
    tacticUnlines = intercalate ";\n"

    -- | Collects all types that occur in an argument of the given constructor.
    getDTypes :: IR.ConDecl -> Converter [IR.QName]
    getDTypes (IR.ConDecl _ _ argTypes) = do
      argTypes' <- mapM expandAllTypeSynonyms argTypes
      concatMapM getDTypes' argTypes'

    -- | Collects all types that occur in the given type.
    getDTypes' :: IR.Type -> Converter [IR.QName]
    getDTypes' (IR.TypeApp _ t1 t2) = do
      ts1 <- getDTypes' t1
      ts2 <- getDTypes' t2
      return (ts1 ++ ts2)
    getDTypes' (IR.TypeCon _ tconName)
      | showPretty tconName == showPretty typeName = return []
      | otherwise = return [tconName]
    getDTypes' (IR.TypeVar _ _) = return []
    getDTypes' (IR.FuncType _ _ _) = return []

  generateProveForallHint1 :: Coq.Qualid -> Coq.Qualid -> Int -> Converter (Coq.Sentence)
  generateProveForallHint1 forType forall nTvars = do
    let tacticConStr   = Text.unpack Coq.Base.proveForall_proveForType
        Just forallStr = Coq.unpackQualid forall
        tactic         = tacticConStr ++ ' ' : forallStr
        underscores    = replicate (3 + 2 * nTvars) Coq.UnderscorePat
        forTypePattern = Coq.ArgsPat forType $ underscores
    return $ Coq.externHint (Just Coq.Global) 0 (Just forTypePattern) tactic [Coq.Base.proveForall_db]

  generateProveForallHint2 :: Coq.Qualid -> Coq.Qualid -> Int -> Coq.Qualid -> Converter (Coq.Sentence)
  generateProveForallHint2 forType forall nTvars inType = localEnv $ do
    hForStr <- freshCoqIdent "HF"
    hInStr  <- freshCoqIdent "HI"
    valStr1 <- freshCoqIdent freshArgPrefix
    valStr2 <- freshCoqIdent freshArgPrefix
    let tacticConStr    = Text.unpack Coq.Base.proveForall_ForType_InType
        Just forStr     = Coq.unpackQualid forType
        Just inStr      = Coq.unpackQualid inType
        Just forallStr  = Coq.unpackQualid forall
        forPatStrs      = forStr : (replicate (2 + 2 * nTvars) "_") ++ ['?':valStr2]
        inPatStrs       = inStr : (replicate (2 + nTvars) "_") ++ ['?':valStr1, '?':valStr2]
        tactic          = unlines
          [ ""
          , "  match goal with"
          , "  | [ " ++ hForStr ++ " : " ++ unwords forPatStrs
          , "    , " ++ hInStr ++ " : " ++ unwords inPatStrs
          , "    |- _ ] =>"
          , "      " ++ unwords [tacticConStr, hForStr, hInStr, valStr1, forallStr]
          , "  end"
          ]
    return $ Coq.externHint (Just Coq.Global) 0 Nothing tactic [Coq.Base.proveForall_db]

  -----------------------------------------------------------------------------
  -- Helper Functions                                                        --
  -----------------------------------------------------------------------------

  -- | The maximal depth to search for recursive occurrences when construction
  --   induction hypotheses.
  --   @0@ -> Create only induction hypotheses for direct recursion.
  --   @n@ -> Create only induction hypotheses for constructor arguments where
  --          the recursive occurrence is encapsulated in at most @n@ data
  --          types.
  maxDepth :: Int
  maxDepth = 1

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

  getForType :: LookupMap Coq.Qualid -> IR.QName -> Converter (Maybe Coq.Qualid)
  getForType forQualidMap name = case forQualidMap Map.!? name of
    Just qualid -> return $ Just qualid
    Nothing     -> inEnv $ lookupForProperty name

  insertPropertiesInEnv :: LookupMap Coq.Qualid -> LookupMap [Coq.Qualid] -> LookupMap Coq.Qualid -> IR.QName -> Converter ()
  insertPropertiesInEnv forQualidMap inQualidMap forallQualidMap name = do
    let forName    = forQualidMap Map.!? name
        inNames    = inQualidMap Map.!? name
        forallName = forallQualidMap Map.!? name
    modifyEnv $ addPropertyNamesToEntry name forName inNames forallName

  generateArg :: String -> Coq.Term -> Converter (Coq.Qualid, Coq.Binder)
  generateArg argName argType = do
    qualid <- freshCoqQualid argName
    let binder = Coq.typedBinder Coq.Ungeneralizable Coq.Explicit [qualid] argType
    return (qualid, binder)
