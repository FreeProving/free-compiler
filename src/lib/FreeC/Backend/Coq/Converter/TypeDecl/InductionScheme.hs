-- | This module contains functions to generate induction schemes for
--   user-defined data types.
module FreeC.Backend.Coq.Converter.TypeDecl.InductionScheme where

import           Control.Monad                    ( mapAndUnzipM, zipWithM )
import qualified Data.Map.Strict                  as Map
import           Data.Maybe
  ( catMaybes, fromJust, fromMaybe )
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

generateInductionSchemes :: [IR.TypeDecl] -> Converter [Coq.Sentence]
generateInductionSchemes dataDecls = do
  let forQualidMap = Map.empty
  schemeQualidMap <- Map.fromList
    <$> mapM (generateName "" "_Ind" . IR.typeDeclQName) dataDecls
  schemeBodies <- mapM (generateSchemeLemma schemeQualidMap forQualidMap)
    dataDecls
  return (map (\(name, binders, term, proof) -> Coq.AssertionSentence
               (Coq.Assertion Coq.Lemma name binders term) proof) schemeBodies)
 where
  -----------------------------------------------------------------------------
  -- Induction Schemes                                                       --
  -----------------------------------------------------------------------------
  -- | Generates an induction scheme for the data type.
  generateSchemeLemma
    :: Map.Map IR.QName Coq.Qualid
    -> Map.Map IR.QName Coq.Qualid
    -> IR.TypeDecl
    -> Converter (Coq.Qualid, [Coq.Binder], Coq.Term, Coq.Proof)
  generateSchemeLemma _ _ (IR.TypeSynDecl _ _ _ _)
    = error "generateInductionLemma: Type synonym not allowed"
  generateSchemeLemma schemeQualidMap forQualidMap
    (IR.DataDecl _ (IR.DeclIdent _ typeName) typeVarDecls conDecls)
    = localEnv $ do
      Just typeQualid <- inEnv $ lookupIdent IR.TypeScope typeName
      (tvarQualids, tvarBinders)
        <- convertTypeVarDecls' Coq.Explicit typeVarDecls
      (propQualid, propBinder) <- generateArg "P"
        (Coq.Arrow (genericApply typeQualid [] [] (map Coq.Qualid tvarQualids))
         (Coq.Sort Coq.Prop))
      indCases <- mapM (generateInductionCase propQualid) conDecls
      (valIdent, valBinder) <- generateArg freshArgPrefix
        (genericApply typeQualid [] [] (map Coq.Qualid tvarQualids))
      (indCaseQualids, fixpointQualid, varQualid) <- localEnv $ do
        indCaseQualids <- mapM (const $ freshCoqQualid "InductionCase") indCases
        fixpointQualid <- freshCoqQualid "FP"
        varQualid <- freshCoqQualid "x"
        return (indCaseQualids, fixpointQualid, varQualid)
      let schemeName = schemeQualidMap Map.! typeName
          binders
            = genericArgDecls Coq.Explicit ++ tvarBinders ++ [propBinder]
          goal       = Coq.forall [valBinder]
            (Coq.app (Coq.Qualid propQualid) [Coq.Qualid valIdent])
          term       = Coq.forall binders (foldr Coq.Arrow goal indCases)
          vars       = map (fromJust . Coq.unpackQualid)
            (Coq.Base.shape
             : Coq.Base.pos
             : tvarQualids ++ [propQualid] ++ indCaseQualids)
          fixpoint   = fromJust $ Coq.unpackQualid fixpointQualid
          var        = fromJust $ Coq.unpackQualid varQualid
          proof      = Coq.ProofQed
            (Text.pack
             $ "  intros"
             ++ concatMap (' ' :) vars
             ++ ";\n"
             ++ "  fix "
             ++ fixpoint
             ++ " 1; intro "
             ++ var
             ++ "; "
             ++ fromJust (Coq.unpackQualid Coq.Base.proveInd)
             ++ ".")
      return (schemeName, [], term, proof)
   where
    -- | Generates an induction case for a given property and constructor.
    generateInductionCase :: Coq.Qualid -> IR.ConDecl -> Converter Coq.Term
    generateInductionCase propQualid
      (IR.ConDecl _ (IR.DeclIdent _ conName) argTypes) = localEnv $ do
        Just conQualid <- inEnv $ lookupIdent IR.ValueScope conName
        argTypes' <- mapM expandAllTypeSynonyms argTypes
        Just conType <- inEnv $ lookupReturnType IR.ValueScope conName
        conType' <- convertType' conType
        (argQualids, argBinders) <- mapAndUnzipM convertAnonymousArg
          (map Just argTypes)
        hypotheses <- catMaybes
          <$> zipWithM (generateInductionHypothesis propQualid conType')
          argQualids argTypes'
        -- Create induction case.
        let term    = foldr Coq.Arrow
              (Coq.app (Coq.Qualid propQualid)
               [Coq.app (Coq.Qualid conQualid) (map Coq.Qualid argQualids)])
              hypotheses
            indCase = Coq.forall argBinders term
        return indCase

    generateInductionHypothesis
      :: Coq.Qualid
      -> Coq.Term
      -> Coq.Qualid
      -> IR.Type
      -> Converter (Maybe Coq.Term)
    generateInductionHypothesis propQualid conType argQualid argType = do
      mbHypothesis <- generateInductionHypothesis_1 1 argType
      argType' <- convertType' argType
      case mbHypothesis of
        Just hypothesis -> return
          $ Just
          $ genericApply Coq.Base.forFree [] []
          [argType', hypothesis, Coq.Qualid argQualid]
        Nothing         -> return Nothing
     where
      generateInductionHypothesis_1
        :: Int -> IR.Type -> Converter (Maybe Coq.Term)
      generateInductionHypothesis_1 _ (IR.FuncType _ _ _)
        = return Nothing
      generateInductionHypothesis_1 md t@(IR.TypeApp _ tcon lastArg) = do
        t' <- convertType' t
        if conType == t'
          then return $ Just $ Coq.Qualid propQualid
          else if md > 0
            then generateInductionHypothesis_2 (md - 1) tcon [lastArg]
            else return Nothing
      generateInductionHypothesis_1 _ t@(IR.TypeCon _ _)             = do
        t' <- convertType' t
        if conType == t'
          then return $ Just $ Coq.Qualid propQualid
          else return Nothing -- Ignore type constructors that do not have any type variable or are partially applied
      generateInductionHypothesis_1 _ (IR.TypeVar _ _)
        = return Nothing

      generateInductionHypothesis_2
        :: Int -> IR.Type -> [IR.Type] -> Converter (Maybe Coq.Term)
      generateInductionHypothesis_2 _ (IR.FuncType _ _ _) _
        = return Nothing
      generateInductionHypothesis_2 md (IR.TypeApp _ tcon lastArg) typeArgs
        = generateInductionHypothesis_2 md tcon (lastArg : typeArgs)
      generateInductionHypothesis_2 md (IR.TypeCon _ tconName) typeArgs     = do
        Just tconArity <- inEnv $ lookupArity IR.TypeScope tconName
        hypotheses <- mapM (generateInductionHypothesis_1 md) typeArgs
        if (tconArity == length typeArgs) && not (null $ catMaybes hypotheses)
          then do
            let hypotheses' = map (fromMaybe (Coq.Qualid Coq.Base.noProperty))
                  hypotheses
            coqArgs <- mapM convertType' typeArgs
            mbForType <- getForType forQualidMap tconName
            return ((\forType ->
                     Just $ genericApply forType [] [] (coqArgs ++ hypotheses'))
                    =<< mbForType)
          else return Nothing
      generateInductionHypothesis_2 _ (IR.TypeVar _ _) _
        = return Nothing

  -----------------------------------------------------------------------------
  -- Helper Functions                                                        --
  -----------------------------------------------------------------------------
  generateName
    :: String -> String -> IR.QName -> Converter (IR.QName, Coq.Qualid)
  generateName prefix suffix typeQName = do
    Just typeQualid <- inEnv $ lookupIdent IR.TypeScope typeQName
    let Just typeIdent = Coq.unpackQualid typeQualid
    newQualid <- freshCoqQualid $ prefix ++ typeIdent ++ suffix
    return (typeQName, newQualid)

  getForType
    :: Map.Map IR.QName Coq.Qualid -> IR.QName -> Converter (Maybe Coq.Qualid)
  getForType forQualidMap t = case forQualidMap Map.!? t of
    Just qualid -> return $ Just qualid
    Nothing     -> do
      -- TODO use environment to store and load other 'For-' properties
      Just qualid <- inEnv $ lookupIdent IR.TypeScope t
      let name      = case qualid of
            Coq.Bare n        -> Text.unpack n
            Coq.Qualified _ n -> Text.unpack n
          mbNewName = case name of
            "List" -> Just "ForList"
            "Pair" -> Just "ForPair"
            _      -> Nothing
      return $ Coq.bare <$> mbNewName

  generateArg :: String -> Coq.Term -> Converter (Coq.Qualid, Coq.Binder)
  generateArg argName argType = do
    qualid <- freshCoqQualid argName
    let binder
          = Coq.typedBinder Coq.Ungeneralizable Coq.Explicit [qualid] argType
    return (qualid, binder)
