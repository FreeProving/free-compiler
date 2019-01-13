module Compiler.HelperFunctionConverter where

import Compiler.HelperFunctions
import Compiler.Types
import Compiler.MonadicConverter

import qualified Language.Coq.Gallina as G
import Language.Haskell.Exts.Syntax

import qualified GHC.Base as B
import Data.Maybe

convertMatchToMainFunction :: Show l => Name l -> [G.Binder] -> G.Term -> [G.TypeSignature] -> [G.Name] -> ConversionMonad -> G.Fixpoint
convertMatchToMainFunction name binders rhs typeSigs dataNames cMonad =
  G.Fixpoint (singleton (G.FixBody funName
    (toNonemptyList bindersWithInferredTypes)
      Nothing
        (Just (transformTermMonadic (getReturnType typeSig) cMonad))
          monadicRhs)) []
  where
    typeSig = fromJust (getTypeSignatureByName typeSigs name)
    funName = addSuffixToName name
    monadicBinders = transformBindersMonadic binders cMonad
    bindersWithInferredTypes = makeMatchedArgNonMonadic (addInferredTypesToSignature monadicBinders dataNames) (binderPos + 1)
    matchItem = getMatchedArgumentFromRhs rhs
    matchedBinder = termToQId (getBinderName (getMatchedBinder binders matchItem))
    binderPos = getMatchedBinderPosition binders matchItem
    monadicArgRhs = switchNonMonadicArgumentsFromTerm rhs (filter (not . eqQId matchedBinder) (map (termToQId . getBinderName) binders)) cMonad
    monadicRhs = addReturnToRhs (addBindOperatorToEquationInMatch monadicArgRhs (nameToQId name) binderPos cMonad) typeSigs bindersWithInferredTypes


convertMatchToHelperFunction :: Show l => Name l -> [G.Binder] -> G.Term -> [G.TypeSignature] -> [G.Name] -> ConversionMonad -> G.Definition
convertMatchToHelperFunction name binders rhs typeSigs dataNames cMonad =
  G.DefinitionDef G.Global
    funName
      bindersWithInferredTypes
        (Just (transformTermMonadic (getReturnType typeSig) cMonad))
          rhsWithBind
  where
    typeSig = fromJust (getTypeSignatureByName typeSigs name)
    funName = nameToQId name
    monadicBinders = transformBindersMonadic binders cMonad
    bindersWithInferredTypes = addInferredTypesToSignature monadicBinders dataNames
    matchItem = getMatchedArgumentFromRhs rhs
    matchedBinder = transformBinderMonadic (getMatchedBinder binders matchItem) cMonad
    binderPos = getMatchedBinderPosition binders matchItem
    appliedMainFunction = G.App (G.Qualid (addSuffixToName name)) (toNonemptyList mainFunArgs)
    mainFunArgs = buildArgsForMainFun monadicBinders binderPos
    rhsWithBind = addBindOperatorToMainFunction (addMonadicPrefixToBinder cMonad matchedBinder) appliedMainFunction

addBindOperatorToMainFunction :: G.Binder -> G.Term -> G.Term
addBindOperatorToMainFunction binder rhs =
  G.App bindOperator
    (toNonemptyList [argumentName, lambdaFun])
  where
    argumentName = G.PosArg (getBinderName binder)
    lambdaFun = G.PosArg (G.Fun (singleton (removeMonadFromBinder binder)) rhs)

addBindOperatorToEquationInMatch :: G.Term -> G.Qualid -> Int -> ConversionMonad -> G.Term
addBindOperatorToEquationInMatch (G.Match mItem retType equations) funName pos m =
  G.Match mItem retType [addBindOperatorToEquation e funName pos m | e <- equations]


addBindOperatorToEquation :: G.Equation -> G.Qualid -> Int -> ConversionMonad -> G.Equation
addBindOperatorToEquation (G.Equation multPats rhs) funName pos m =
  if containsRecursiveCall rhs funName
    then G.Equation (toNonemptyList (makeDecrArgumentMonadicInMultPats (nonEmptyListToList multPats) decrArgument m))
          (addBindOperatorToRecursiveCall rhs funName pos m)
    else G.Equation multPats rhs
  where
    decrArgument = getDecrArgumentFromRecursiveCall rhs funName pos

addBindOperatorToRecursiveCall :: G.Term -> G.Qualid -> Int -> ConversionMonad -> G.Term
addBindOperatorToRecursiveCall (G.App constr args) funName pos m =
  if containsRecursiveCall constr funName
    then G.App bindOperator (toNonemptyList [ monadicArgument, lambdaFun])
    else G.App constr (toNonemptyList checkedArgs)
  where
    monadicArgument = G.PosArg (G.Qualid (addMonadicPrefixToQId m decrArgument))
    lambdaFun = G.PosArg (G.Fun (singleton (G.Inferred G.Explicit (qIdToGName decrArgument))) recCall)
    recCall = G.App (addSuffixToTerm constr) args
    decrArgument = termToQId (argToTerm (nonEmptyListToList args !! pos))
    termList = convertArgumentsToTerms (nonEmptyListToList args)
    checkedArgs = convertTermsToArguments [addBindOperatorToRecursiveCall t funName pos m| t <- termList]
addBindOperatorToRecursiveCall (G.Parens term) funName pos m =
  G.Parens (addBindOperatorToRecursiveCall term funName pos m)
addBindOperatorToRecursiveCall term _ _ _ =
  term

getDecrArgumentFromRecursiveCall :: G.Term -> G.Qualid -> Int -> Maybe G.Qualid
getDecrArgumentFromRecursiveCall (G.App constr args) funName pos =
  if containsRecursiveCall constr funName
    then Just decrArgument
    else head (filter isJust [getDecrArgumentFromRecursiveCall t funName pos | t <- termList])
  where
    termList = convertArgumentsToTerms (nonEmptyListToList args)
    decrArgument = termToQId (argToTerm (nonEmptyListToList args !! pos))
getDecrArgumentFromRecursiveCall (G.Parens term) funName pos =
  getDecrArgumentFromRecursiveCall term funName pos
getDecrArgumentFromRecursiveCall _ _ _ = Nothing

makeDecrArgumentMonadicInMultPats :: [G.MultPattern] -> Maybe G.Qualid -> ConversionMonad -> [G.MultPattern]
makeDecrArgumentMonadicInMultPats [G.MultPattern nEPats] (Just decrArgument) m =
  [G.MultPattern (toNonemptyList (makeDecrArgumentMonadicInPats pats decrArgument m))]
  where
    pats = nonEmptyListToList nEPats

makeDecrArgumentMonadicInPats :: [G.Pattern] -> G.Qualid -> ConversionMonad -> [G.Pattern]
makeDecrArgumentMonadicInPats [G.ArgsPat qId pats] decrArgument m =
  if eqQId qId decrArgument
    then [G.ArgsPat (addMonadicPrefixToQId m qId) pats]
    else [G.ArgsPat qId (makeDecrArgumentMonadicInPats pats decrArgument m)]
makeDecrArgumentMonadicInPats (G.QualidPat qId : ps) decrArgument m =
  if eqQId qId decrArgument
    then [G.QualidPat (addMonadicPrefixToQId m qId)]
    else G.QualidPat qId : makeDecrArgumentMonadicInPats ps decrArgument m
makeDecrArgumentMonadicInPats pats _ _ =
  pats

buildArgsForMainFun :: [G.Binder] -> Int -> [G.Arg]
buildArgsForMainFun binders pos =
  buildArgsForMainFun' binders pos 0

buildArgsForMainFun' :: [G.Binder] -> Int -> Int -> [G.Arg]
buildArgsForMainFun' (b : bs) pos currentPos =
  if pos == currentPos
    then G.PosArg (getBinderName (removeMonadFromBinder b)) :
          buildArgsForMainFun' bs pos (currentPos + 1)
    else G.PosArg (getBinderName b) :
          buildArgsForMainFun' bs pos (currentPos + 1)
buildArgsForMainFun' [] _ _ = []

makeMatchedArgNonMonadic :: [G.Binder] -> Int -> [G.Binder]
makeMatchedArgNonMonadic binders pos =
  makeMatchedArgNonMonadic' binders pos 0

makeMatchedArgNonMonadic' :: [G.Binder] -> Int -> Int -> [G.Binder]
makeMatchedArgNonMonadic' (b : bs) pos currentPos =
  if pos == currentPos
    then removeMonadFromBinder b : makeMatchedArgNonMonadic' bs pos (currentPos + 1)
    else b : makeMatchedArgNonMonadic' bs pos (currentPos + 1)
makeMatchedArgNonMonadic' [] _ _ = []

addSuffixToName :: Show l => Name l -> G.Qualid
addSuffixToName name =
  strToQId (nameToStr name ++ "'")

addSuffixToTerm :: G.Term -> G.Term
addSuffixToTerm (G.Qualid qId) =
  G.Qualid (strToQId (qIdToStr qId ++ "'"))

getMatchedBinder :: [G.Binder] -> G.Term -> G.Binder
getMatchedBinder (b : bs) matchItem =
  if isMatchedBinder b matchItem
    then b
    else getMatchedBinder bs matchItem
getMatchedBinder [] _ =
  error "matchItem doesn't match any binder"

getMatchedBinderPosition :: [G.Binder] -> G.Term -> Int
getMatchedBinderPosition binders matchItem =
  getMatchedBinderPosition' binders matchItem 0

switchNonMonadicArgumentsFromTerm :: G.Term -> [G.Qualid] -> ConversionMonad -> G.Term
switchNonMonadicArgumentsFromTerm (G.Match mItem retType equations) binders m =
  G.Match mItem retType [switchNonMonadicArgumentsFromEquation e binders m | e <- equations]
switchNonMonadicArgumentsFromTerm (G.App constr args) binders m =
  G.App (switchNonMonadicArgumentsFromTerm constr binders m)
    (toNonemptyList [(\(G.PosArg term) -> G.PosArg (switchNonMonadicArgumentsFromTerm term binders m)) a | a <- nonEmptyListToList args])
switchNonMonadicArgumentsFromTerm (G.Parens term) binders m =
  G.Parens (switchNonMonadicArgumentsFromTerm term binders m)
switchNonMonadicArgumentsFromTerm (G.Qualid qId) binders m =
  if any (eqQId qId) binders
    then G.Qualid (addMonadicPrefixToQId m qId)
    else G.Qualid qId

switchNonMonadicArgumentsFromEquation :: G.Equation -> [G.Qualid] -> ConversionMonad -> G.Equation
switchNonMonadicArgumentsFromEquation (G.Equation pat rhs) binders m =
  G.Equation pat (switchNonMonadicArgumentsFromTerm rhs binders m)


getMatchedBinderPosition' :: [G.Binder] -> G.Term -> Int -> Int
getMatchedBinderPosition' (b : bs) matchItem pos =
  if isMatchedBinder b matchItem
    then pos
    else getMatchedBinderPosition' bs matchItem (pos + 1)
getMatchedBinderPosition' [] _ _ =
  error "matchItem doesn't match any binder"

getMatchedArgumentFromRhs :: G.Term -> G.Term
getMatchedArgumentFromRhs (G.Match (G.MatchItem term _ _ B.:| ms) _ _ ) =
  term
getMatchedArgumentFromRhs _ = error "recursive functions only work woth pattern-matching"

isMatchedBinder :: G.Binder -> G.Term -> Bool
isMatchedBinder (G.Typed _ _ (name B.:| _) _ ) (G.Qualid qId) =
  eqQId (gNameToQId name) qId
