module Compiler.HelperFunctionConverter where

import           Compiler.HelperFunctions       ( addInferredTypesToSignature
                                                , argToTerm
                                                , containsMatchTerm
                                                , containsRecursiveCall
                                                , convertArgumentsToTerms
                                                , convertTermsToArguments
                                                , eqBinder
                                                , eqQId
                                                , gNameToQId
                                                , getBinderName
                                                , getMatchFromTerm
                                                , getMatchItem
                                                , getReturnType
                                                , getTermFromMatchItem
                                                , getTypeSignatureByName
                                                , nameToQId
                                                , nameToStr
                                                , qIdToGName
                                                , qIdToStr
                                                , strToQId
                                                , termToQId
                                                )
import           Compiler.Language.Coq.TypeSignature
import           Compiler.MonadicConverter      ( addMonadicPrefixToBinder
                                                , addMonadicPrefixToQId
                                                , addReturnToRhs
                                                , getBindOperator
                                                , isMonadicArrowTerm
                                                , removeMonadFromBinder
                                                , transformBinderMonadic
                                                , transformBindersMonadic
                                                , transformTermMonadic
                                                )
import           Compiler.NonEmptyList          ( fromNonEmptyList
                                                , singleton
                                                , toNonEmptyList
                                                )
import           Compiler.Types                 ( ConversionMonad(..) )

import qualified Language.Coq.Gallina          as G
import qualified Language.Haskell.Exts.Syntax  as H

import           Data.Maybe                     ( fromJust
                                                , isJust
                                                )
import qualified GHC.Base                      as B

convertMatchToMainFunction
  :: Show l
  => H.Name l
  -> [G.Binder]
  -> G.Term
  -> [TypeSignature]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  -> ConversionMonad
  -> G.Fixpoint
convertMatchToMainFunction name binders rhs typeSigs dataTypes cMonad =
  G.Fixpoint
    (singleton
      (G.FixBody funName
                 (toNonEmptyList bindersWithFixedArguments)
                 Nothing
                 (Just (transformTermMonadic (getReturnType typeSig) cMonad))
                 monadicRhs
      )
    )
    []
 where
  typeSig                  = fromJust (getTypeSignatureByName typeSigs name)
  funName                  = addSuffixToName name
  monadicBinders           = transformBindersMonadic binders cMonad
  bindersWithInferredTypes = addInferredTypesToSignature
    monadicBinders
    (map fst dataTypes)
    (getReturnType typeSig)
  bindersWithFixedArguments =
    if length binders == length bindersWithInferredTypes
      then makeMatchedArgNonMonadic bindersWithInferredTypes binderPos
      else makeMatchedArgNonMonadic bindersWithInferredTypes (binderPos + 1)
  matchItem     = getMatchedArgumentFromRhs rhs
  matchedBinder = getMatchedBinder binders matchItem
  binderPos     = getMatchedBinderPosition binders matchItem
  monadicArgRhs = switchNonMonadicArgumentsFromTerm
    rhs
    (filter (not . eqBinder matchedBinder) binders)
    cMonad
  monadicRhs = addReturnToRhs
    (addBindOperatorToRhsTerm (nameToQId name) binderPos cMonad monadicArgRhs)
    typeSigs
    bindersWithInferredTypes
    dataTypes
    cMonad

convertMatchToHelperFunction
  :: Show l
  => H.Name l
  -> [G.Binder]
  -> G.Term
  -> [TypeSignature]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  -> ConversionMonad
  -> G.Definition
convertMatchToHelperFunction name binders rhs typeSigs dataTypes cMonad =
  G.DefinitionDef G.Global
                  funName
                  bindersWithInferredTypes
                  (Just (transformTermMonadic (getReturnType typeSig) cMonad))
                  rhsWithBind
 where
  typeSig                  = fromJust (getTypeSignatureByName typeSigs name)
  funName                  = nameToQId name
  monadicBinders           = transformBindersMonadic binders cMonad
  bindersWithInferredTypes = addInferredTypesToSignature
    monadicBinders
    (map fst dataTypes)
    (getReturnType typeSig)
  matchItem = getMatchedArgumentFromRhs rhs
  matchedBinder =
    transformBinderMonadic (getMatchedBinder binders matchItem) cMonad
  binderPos = getMatchedBinderPosition binders matchItem
  appliedMainFunction =
    G.App (G.Qualid (addSuffixToName name)) (toNonEmptyList mainFunArgs)
  mainFunArgs = buildArgsForMainFun monadicBinders binderPos
  rhsWithBind = addBindOperatorToMainFunction
    (addMonadicPrefixToBinder cMonad matchedBinder)
    appliedMainFunction
    cMonad

addBindOperatorToMainFunction :: G.Binder -> G.Term -> ConversionMonad -> G.Term
addBindOperatorToMainFunction binder rhs cMonad = G.App
  (getBindOperator cMonad)
  (toNonEmptyList [argumentName, lambdaFun])
 where
  argumentName = G.PosArg (getBinderName binder)
  lambdaFun    = G.PosArg (G.Fun (singleton (removeMonadFromBinder binder)) rhs)

addBindOperatorToRhsTerm
  :: G.Qualid -> Int -> ConversionMonad -> G.Term -> G.Term
addBindOperatorToRhsTerm funName pos m (G.If style cond depRet tTerm eTerm) =
  G.If style
       (addBindOperatorToRhsTerm funName pos m cond)
       depRet
       (addBindOperatorToRhsTerm funName pos m tTerm)
       (addBindOperatorToRhsTerm funName pos m eTerm)
addBindOperatorToRhsTerm funName pos m (G.Match mItem retType equations) =
  G.Match mItem
          retType
          [ addBindOperatorToEquation e funName pos m | e <- equations ]
addBindOperatorToRhsTerm funName pos m (G.App constr args) = G.App
  boundConstr
  (toNonEmptyList boundArgs)
 where
  boundConstr = addBindOperatorToRhsTerm funName pos m constr
  boundArgs   = map
    G.PosArg
    (map (addBindOperatorToRhsTerm funName pos m)
         (map argToTerm (fromNonEmptyList args))
    )
addBindOperatorToRhsTerm _ _ _ term = term

addBindOperatorToEquation
  :: G.Equation -> G.Qualid -> Int -> ConversionMonad -> G.Equation
addBindOperatorToEquation (G.Equation multPats rhs) funName pos m =
  if containsRecursiveCall rhs funName
    then if containsMatchTerm rhs
      then G.Equation
        (toNonEmptyList
          (makeDecrArgumentMonadicInMultPats (fromNonEmptyList multPats)
                                             matchedItem
                                             m
          )
        )
        boundMatchedRhs
      else G.Equation
        (toNonEmptyList
          (makeDecrArgumentMonadicInMultPats (fromNonEmptyList multPats)
                                             decrArgument
                                             m
          )
        )
        (addBindOperatorToRecursiveCall rhs funName pos m)
    else G.Equation multPats rhs
 where
  decrArgument = getDecrArgumentFromRecursiveCall rhs funName pos
  matchedItem =
    (Just . termToQId . getTermFromMatchItem . getMatchItem . getMatchFromTerm)
      rhs
  boundMatchedRhs = addBindOperatorToMatchItem m boundRecCallRhs
  boundRecCallRhs = addBindOperatorToRhsTerm funName pos m rhs

addBindOperatorToMatchItem :: ConversionMonad -> G.Term -> G.Term
addBindOperatorToMatchItem m (G.Parens term) =
  G.Parens (addBindOperatorToMatchItem m term)
addBindOperatorToMatchItem m (G.App cons args) = G.App
  (addBindOperatorToMatchItem m cons)
  (toNonEmptyList checkedArgs)
 where
  checkedArgs = map (G.PosArg . addBindOperatorToMatchItem m . argToTerm)
                    (fromNonEmptyList args)
addBindOperatorToMatchItem m (G.If style cond depRet tTerm eTerm) = G.If
  style
  (addBindOperatorToMatchItem m cond)
  depRet
  (addBindOperatorToMatchItem m tTerm)
  (addBindOperatorToMatchItem m eTerm)
addBindOperatorToMatchItem m (G.Match mItem retType equations) = G.App
  (getBindOperator m)
  (toNonEmptyList [monadicArgument, lambdaFun])
 where
  mItemTerm = (getTermFromMatchItem . head . fromNonEmptyList) mItem
  monadicArgument =
    (G.PosArg . G.Qualid . addMonadicPrefixToQId m . termToQId) mItemTerm
  lambdaFun = G.PosArg
    (G.Fun
      (singleton (G.Inferred G.Explicit ((qIdToGName . termToQId) mItemTerm)))
      (G.Match mItem retType equations)
    )
addBindOperatorToMatchItem _ term = term

addBindOperatorToRecursiveCall
  :: G.Term -> G.Qualid -> Int -> ConversionMonad -> G.Term
addBindOperatorToRecursiveCall (G.App constr args) funName pos m =
  if containsRecursiveCall constr funName
    then G.App (getBindOperator m) (toNonEmptyList [monadicArgument, lambdaFun])
    else G.App constr (toNonEmptyList checkedArgs)
 where
  monadicArgument = G.PosArg (G.Qualid (addMonadicPrefixToQId m decrArgument))
  lambdaFun       = G.PosArg
    (G.Fun (singleton (G.Inferred G.Explicit (qIdToGName decrArgument))) recCall
    )
  recCall      = G.App (addSuffixToTerm constr) args
  decrArgument = termToQId (argToTerm (fromNonEmptyList args !! pos))
  termList     = convertArgumentsToTerms (fromNonEmptyList args)
  checkedArgs  = convertTermsToArguments
    [ addBindOperatorToRecursiveCall t funName pos m | t <- termList ]
addBindOperatorToRecursiveCall (G.Parens term) funName pos m =
  G.Parens (addBindOperatorToRecursiveCall term funName pos m)
addBindOperatorToRecursiveCall (G.If style cond depRet tTerm eTerm) funName pos m
  = G.If style
         (addBindOperatorToRecursiveCall cond funName pos m)
         depRet
         (addBindOperatorToRecursiveCall tTerm funName pos m)
         (addBindOperatorToRecursiveCall eTerm funName pos m)
addBindOperatorToRecursiveCall term funName pos m =
  addBindOperatorToRhsTerm funName pos m term

getDecrArgumentFromRecursiveCall :: G.Term -> G.Qualid -> Int -> Maybe G.Qualid
getDecrArgumentFromRecursiveCall (G.App constr args) funName pos =
  if containsRecursiveCall constr funName
    then Just decrArgument
    else
      if null
           (filter
             isJust
             [ getDecrArgumentFromRecursiveCall t funName pos | t <- termList ]
           )
        then Nothing
        else head
          (filter
            isJust
            [ getDecrArgumentFromRecursiveCall t funName pos | t <- termList ]
          )
 where
  termList     = convertArgumentsToTerms (fromNonEmptyList args)
  decrArgument = termToQId (argToTerm (fromNonEmptyList args !! pos))
getDecrArgumentFromRecursiveCall (G.Parens term) funName pos =
  getDecrArgumentFromRecursiveCall term funName pos
getDecrArgumentFromRecursiveCall (G.If _ cond _ tTerm eTerm) funName pos =
  if containsRecursiveCall cond funName
    then getDecrArgumentFromRecursiveCall cond funName pos
    else if containsRecursiveCall tTerm funName
      then getDecrArgumentFromRecursiveCall tTerm funName pos
      else getDecrArgumentFromRecursiveCall eTerm funName pos
getDecrArgumentFromRecursiveCall _ _ _ = Nothing

makeDecrArgumentMonadicInMultPats
  :: [G.MultPattern] -> Maybe G.Qualid -> ConversionMonad -> [G.MultPattern]
makeDecrArgumentMonadicInMultPats [G.MultPattern nEPats] (Just decrArgument) m
  = [ G.MultPattern
        (toNonEmptyList (makeDecrArgumentMonadicInPats pats decrArgument m))
    ]
  where pats = fromNonEmptyList nEPats
makeDecrArgumentMonadicInMultPats mPats _ _ = mPats

makeDecrArgumentMonadicInPats
  :: [G.Pattern] -> G.Qualid -> ConversionMonad -> [G.Pattern]
makeDecrArgumentMonadicInPats [G.ArgsPat qId pats] decrArgument m =
  if eqQId qId decrArgument
    then [G.ArgsPat (addMonadicPrefixToQId m qId) pats]
    else [G.ArgsPat qId (makeDecrArgumentMonadicInPats pats decrArgument m)]
makeDecrArgumentMonadicInPats (G.QualidPat qId : ps) decrArgument m =
  if eqQId qId decrArgument
    then [G.QualidPat (addMonadicPrefixToQId m qId)]
    else G.QualidPat qId : makeDecrArgumentMonadicInPats ps decrArgument m
makeDecrArgumentMonadicInPats pats _ _ = pats

buildArgsForMainFun :: [G.Binder] -> Int -> [G.Arg]
buildArgsForMainFun binders pos = buildArgsForMainFun' binders pos 0

buildArgsForMainFun' :: [G.Binder] -> Int -> Int -> [G.Arg]
buildArgsForMainFun' (b : bs) pos currentPos = if pos == currentPos
  then G.PosArg (getBinderName (removeMonadFromBinder b))
    : buildArgsForMainFun' bs pos (currentPos + 1)
  else G.PosArg (getBinderName b) : buildArgsForMainFun' bs pos (currentPos + 1)
buildArgsForMainFun' [] _ _ = []

makeMatchedArgNonMonadic :: [G.Binder] -> Int -> [G.Binder]
makeMatchedArgNonMonadic binders pos = makeMatchedArgNonMonadic' binders pos 0

makeMatchedArgNonMonadic' :: [G.Binder] -> Int -> Int -> [G.Binder]
makeMatchedArgNonMonadic' (b : bs) pos currentPos = if pos == currentPos
  then removeMonadFromBinder b
    : makeMatchedArgNonMonadic' bs pos (currentPos + 1)
  else b : makeMatchedArgNonMonadic' bs pos (currentPos + 1)
makeMatchedArgNonMonadic' [] _ _ = []

addSuffixToName :: Show l => H.Name l -> G.Qualid
addSuffixToName name = strToQId (nameToStr name ++ "'")

addSuffixToTerm :: G.Term -> G.Term
addSuffixToTerm (G.Qualid qId) = G.Qualid (strToQId (qIdToStr qId ++ "'"))
addSuffixToTerm term           = term

getMatchedBinder :: [G.Binder] -> G.Term -> G.Binder
getMatchedBinder (b : bs) matchItem =
  if isMatchedBinder b matchItem then b else getMatchedBinder bs matchItem
getMatchedBinder [] _ = error "matchItem doesn't match any binder"

getMatchedBinderPosition :: [G.Binder] -> G.Term -> Int
getMatchedBinderPosition binders matchItem =
  getMatchedBinderPosition' binders matchItem 0

switchNonMonadicArgumentsFromTerm
  :: G.Term -> [G.Binder] -> ConversionMonad -> G.Term
switchNonMonadicArgumentsFromTerm (G.Match mItem retType equations) binders m =
  G.Match
    mItem
    retType
    [ switchNonMonadicArgumentsFromEquation e binders m | e <- equations ]
switchNonMonadicArgumentsFromTerm (G.App constr args) binders m = G.App
  (switchNonMonadicArgumentsFromTerm constr binders m)
  (toNonEmptyList
    [ (\(G.PosArg term) ->
        G.PosArg (switchNonMonadicArgumentsFromTerm term binders m)
      )
        a
    | a <- fromNonEmptyList args
    ]
  )
switchNonMonadicArgumentsFromTerm (G.Parens term) binders m =
  G.Parens (switchNonMonadicArgumentsFromTerm term binders m)
switchNonMonadicArgumentsFromTerm (G.Qualid qId) binders m =
  if any (eqQId qId) (map (termToQId . getBinderName) binders)
       && not (isMonadicArrowTerm (G.Qualid qId) binders)
    then G.Qualid (addMonadicPrefixToQId m qId)
    else G.Qualid qId
switchNonMonadicArgumentsFromTerm (G.If style cond depRet thenTerm elseTerm) binders m
  = G.If style
         (switchNonMonadicArgumentsFromTerm cond binders m)
         depRet
         (switchNonMonadicArgumentsFromTerm thenTerm binders m)
         (switchNonMonadicArgumentsFromTerm elseTerm binders m)

switchNonMonadicArgumentsFromEquation
  :: G.Equation -> [G.Binder] -> ConversionMonad -> G.Equation
switchNonMonadicArgumentsFromEquation (G.Equation pat rhs) binders m =
  G.Equation pat (switchNonMonadicArgumentsFromTerm rhs binders m)

getMatchedBinderPosition' :: [G.Binder] -> G.Term -> Int -> Int
getMatchedBinderPosition' (b : bs) matchItem pos =
  if isMatchedBinder b matchItem
    then pos
    else getMatchedBinderPosition' bs matchItem (pos + 1)
getMatchedBinderPosition' [] _ _ = error "matchItem doesn't match any binder"

getMatchedArgumentFromRhs :: G.Term -> G.Term
getMatchedArgumentFromRhs (G.Match (G.MatchItem term _ _ B.:| _) _ _) = term
getMatchedArgumentFromRhs (G.App _ (_ B.:| y : _)) =
  getMatchedArgumentFromRhs (argToTerm y)
getMatchedArgumentFromRhs term =
  error ("recursive functions only work with pattern-matching" ++ show term)

isMatchedBinder :: G.Binder -> G.Term -> Bool
isMatchedBinder (G.Typed _ _ (name B.:| _) _) (G.Qualid qId) =
  eqQId (gNameToQId name) qId
