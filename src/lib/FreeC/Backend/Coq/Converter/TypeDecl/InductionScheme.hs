-- | This module contains functions to generate induction schemes for
--   user-defined data types.
module FreeC.Backend.Coq.Converter.TypeDecl.InductionScheme
  ( generateInductionScheme
  ) where

import           Control.Monad                    ( mapAndUnzipM )
import qualified Data.List.NonEmpty               as NonEmpty
import           Data.Maybe                       ( fromJust )
import qualified Data.Text                        as Text

import qualified FreeC.Backend.Coq.Base           as Coq.Base
import           FreeC.Backend.Coq.Converter.Arg
import           FreeC.Backend.Coq.Converter.Free
import           FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Syntax         as Coq
import           FreeC.Environment
import           FreeC.Environment.Fresh
  ( freshArgPrefix, freshCoqIdent, freshCoqQualid )
import qualified FreeC.IR.Syntax                  as IR
import           FreeC.Monad.Converter

-- | Generates an induction scheme for the given data type.
generateInductionScheme :: IR.TypeDecl -> Converter [Coq.Sentence]
generateInductionScheme
  (IR.DataDecl _ (IR.DeclIdent _ name) typeVarDecls conDecls) = localEnv $ do
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
    schemeName <- freshCoqQualid $ fromJust (Coq.unpackQualid tIdent) ++ "_ind"
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
-- Type synonyms are not allowed in this function.
generateInductionScheme (IR.TypeSynDecl _ _ _ _)
  = error "generateInductionScheme: Type synonym not allowed."

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
      | argType == fConType = Coq.Arrow (genericForFree conType pIdent argIdent)
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
