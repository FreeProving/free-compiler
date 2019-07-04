module Compiler.Converter.MonadicConverter where

import           Language.Coq.Gallina          as G
import           Language.Coq.Gallina.Util      ( qualidIsOp )

import           Compiler.Converter.HelperFunctions
                                                ( addSuffixToQId
                                                , containsAllConstrs
                                                , containsMatchTerm
                                                , convertArgumentsToTerms
                                                , eqQId
                                                , gNameToQId
                                                , getBinderByQId
                                                , getBinderName
                                                , getBinderType
                                                , getConstrsByPattern
                                                , getPatternFromEquation
                                                , getPatternFromMultPattern
                                                , getQIdsFromPattern
                                                , getStringFromGName
                                                , getTermFromMatchItem
                                                , getTypeSignatureByQId
                                                , isArrowTerm
                                                , isUnderscorePat
                                                , qIdToGName
                                                , qIdToStr
                                                , strToGName
                                                , strToQId
                                                , termToQId
                                                , typeTerm
                                                )
import           Compiler.Language.Coq.TypeSignature
import           Compiler.Util.Data.List.NonEmpty
                                                ( fromNonEmptyList
                                                , singleton
                                                , toNonEmptyList
                                                )
import           Compiler.Converter.Types       ( ConversionMonad(..) )

import           Data.Maybe                     ( fromJust
                                                , isJust
                                                )
import qualified Data.Text                     as T
import qualified GHC.Base                      as B

---------------------- Add Bind Operator to Definition
addBindOperatorsToDefinition
  :: [G.Binder] -> G.Term -> ConversionMonad -> G.Term
addBindOperatorsToDefinition [] term cMonad = addBindOperatorsInRhs term cMonad
addBindOperatorsToDefinition (x : xs) term cMonad =
  if isArrowTerm (getBinderType x)
    then addBindOperatorsToDefinition xs term cMonad
    else G.App (getBindOperator cMonad)
               (toNonEmptyList [G.PosArg argumentName, G.PosArg lambdaFun])
 where
  argumentName = getBinderName x
  lambdaFun    = G.Fun (singleton (removeMonadFromBinder x))
                       (addBindOperatorsToDefinition xs term cMonad)

addBindOperatorsInRhs :: G.Term -> ConversionMonad -> G.Term
addBindOperatorsInRhs (G.Match mItem retType equations) cMonad =
  G.Match mItem retType [ addBindOperatorsInEquation e cMonad | e <- equations ]
addBindOperatorsInRhs term _ = term

addBindOperatorsInEquation :: G.Equation -> ConversionMonad -> G.Equation
addBindOperatorsInEquation (G.Equation multPats rhs) cMonad = G.Equation
  multPats
  (addBindOpperatorsInMatchRhs ((head . fromNonEmptyList) multPats) cMonad rhs)

addBindOpperatorsInMatchRhs
  :: G.MultPattern -> ConversionMonad -> G.Term -> G.Term
addBindOpperatorsInMatchRhs multPats cMonad (G.App constr args) = G.App
  constr
  (toNonEmptyList boundArgs)
 where
  boundArgs = map (G.PosArg . addBindOpperatorsInMatchRhs multPats cMonad)
                  (convertArgumentsToTerms (fromNonEmptyList args))
addBindOpperatorsInMatchRhs multPats cMonad (G.Match mItem retType equations) =
  if any (eqQId (termToQId argumentName))
         (concatMap getQIdsFromPattern (getPatternFromMultPattern (multPats)))
    then G.App
      (getBindOperator cMonad)
      (toNonEmptyList
        [ G.PosArg argumentName
        , G.PosArg (G.Fun (singleton lambdaBinder) lambdaTerm)
        ]
      )
    else G.Match mItem retType boundEquations
 where
  argumentName      = (getTermFromMatchItem . head . fromNonEmptyList) mItem
  lambdaArgumentQId = (addSuffixToQId . termToQId) argumentName
  boundMatchItem    = G.MatchItem (G.Qualid lambdaArgumentQId) Nothing Nothing
  lambdaBinder      = G.Inferred G.Explicit (qIdToGName lambdaArgumentQId)
  lambdaTerm        = G.Match (singleton boundMatchItem) retType boundEquations
  boundEquations    = [ addBindOperatorsInEquation e cMonad | e <- equations ]
addBindOpperatorsInMatchRhs _ _ term = term

---------------------- Add Return Operator if rhs isn't already monadic
addReturnToRhs
  :: G.Term
  -> [TypeSignature]
  -> [G.Binder]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  -> ConversionMonad
  -> G.Term
addReturnToRhs (G.Match mItem retType equations) typeSigs binders dataTypes cMonad
  = addReturnToMatch (G.Match mItem retType equations)
                     typeSigs
                     binders
                     dataTypes
                     []
                     cMonad
addReturnToRhs rhs typeSigs binders dataTypes cMonad =
  addReturnToTerm rhs typeSigs binders dataTypes [] cMonad

addReturnToMatch
  :: G.Term
  -> [TypeSignature]
  -> [G.Binder]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  -> [G.Qualid]
  -> ConversionMonad
  -> G.Term
addReturnToMatch (G.Match mItem retType equations) typeSigs binders dataTypes patNames cMonad
  = if any isUnderscorePat equationPats
       || isJust constructors
       && containsAllConstrs equationPats (fromJust constructors)
    then
      G.Match mItem retType monadicEquations
    else
      G.Match mItem retType (monadicEquations ++ errorEquation cMonad)
 where
  monadicEquations =
    [ addReturnToEquation e typeSigs binders dataTypes patNames cMonad
    | e <- equations
    ]
  constrNames  = (map ((map fst) . snd) dataTypes)
  equationPats = map (head . getPatternFromEquation) equations
  constructors = getConstrsByPattern (head equationPats) constrNames

addReturnToEquation
  :: G.Equation
  -> [TypeSignature]
  -> [G.Binder]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  -> [G.Qualid]
  -> ConversionMonad
  -> G.Equation
addReturnToEquation (G.Equation multPats rhs) typeSigs binders dataTypes prevPatNames cMonad
  = G.Equation
    multPats
    (addReturnToTerm rhs typeSigs binders dataTypes patNames cMonad)
 where
  pats     = concatMap getPatternFromMultPattern (fromNonEmptyList multPats)
  patNames = prevPatNames ++ concatMap getQIdsFromPattern pats

addReturnToTerm
  :: G.Term
  -> [TypeSignature]
  -> [G.Binder]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  -> [G.Qualid]
  -> ConversionMonad
  -> G.Term
addReturnToTerm (G.App constr args) typeSigs binders dataTypes patNames cMonad
  | isMonadicTerm constr
    || isMonadicFunctionCall constr typeSigs
    || isMonadicBinder constr binders
    || isMonadicArrowTerm constr binders
  = G.App constr fixedArgs
  | qualidIsOp (termToQId constr)
  = toReturnTerm (G.App constr args) cMonad
  | otherwise
  = toReturnTerm (G.App constr fixedArgs) cMonad
 where
  fixedArgs = toNonEmptyList
    (addReturnToArgs (fromNonEmptyList args)
                     typeSigs
                     binders
                     dataTypes
                     patNames
                     cMonad
    )
addReturnToTerm (G.If style cond depRet thenTerm elseTerm) typeSigs binders dataNames patNames cMonad
  = G.If style
         (addReturnToTerm cond typeSigs binders dataNames patNames cMonad)
         depRet
         (addReturnToTerm thenTerm typeSigs binders dataNames patNames cMonad)
         (addReturnToTerm elseTerm typeSigs binders dataNames patNames cMonad)
addReturnToTerm (G.Parens term) typeSigs binders dataNames patNames cMonad =
  G.Parens (addReturnToTerm term typeSigs binders dataNames patNames cMonad)
addReturnToTerm (G.Fun fBinders term) typeSigs binders dataNames patNames cMonad
  = if containsMatchTerm term
    then G.Fun
      fBinders
      (addReturnToTerm term typeSigs binders dataNames patNames cMonad)
    else G.Fun fBinders term
addReturnToTerm (G.Match mItem retType equations) typeSigs binders dataNames patNames cMonad
  = addReturnToMatch (G.Match mItem retType equations)
                     typeSigs
                     binders
                     dataNames
                     patNames
                     cMonad
addReturnToTerm term typeSigs binders _ patNames cMonad =
  if isMonadicTerm term
       || isMonadicFunctionCall term typeSigs
       || isMonadicBinder term binders
       || isPatName term patNames
       || isMonadicArrowTerm term binders
    then term
    else toReturnTerm term cMonad

addReturnToArgs
  :: [G.Arg]
  -> [TypeSignature]
  -> [G.Binder]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  -> [G.Qualid]
  -> ConversionMonad
  -> [G.Arg]
addReturnToArgs (x : xs) typeSigs binders dataTypes patNames cMonad =
  addReturnToArg x typeSigs binders dataTypes patNames cMonad
    : addReturnToArgs xs typeSigs binders dataTypes patNames cMonad
addReturnToArgs [] _ _ _ _ _ = []

addReturnToArg
  :: G.Arg
  -> [TypeSignature]
  -> [G.Binder]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  -> [G.Qualid]
  -> ConversionMonad
  -> G.Arg
addReturnToArg (G.PosArg term) typeSigs binders dataTypes patNames cMonad =
  G.PosArg (addReturnToTerm term typeSigs binders dataTypes patNames cMonad)

---------------------- transform Data Structures Monadic
transformBindersMonadic :: [G.Binder] -> ConversionMonad -> [G.Binder]
transformBindersMonadic binders m =
  [ transformBinderMonadic (addMonadicPrefixToBinder m b) m | b <- binders ]

transformBinderMonadic :: G.Binder -> ConversionMonad -> G.Binder
transformBinderMonadic (G.Typed gen expl name term) m =
  G.Typed gen expl name (transformTermMonadic term m)

transformTermMonadic :: G.Term -> ConversionMonad -> G.Term
transformTermMonadic (G.Sort G.Type) _ = typeTerm
transformTermMonadic (G.Parens term) m = G.Parens (transformTermMonadic term m)
transformTermMonadic (G.Arrow term1 term2) m =
  G.Arrow (transformTermMonadic term1 m) (transformTermMonadic term2 m)
transformTermMonadic term m = monad term where monad = getMonadFun m

getMonadFun :: ConversionMonad -> (G.Term -> G.Term)
getMonadFun m = case m of
  Option   -> toOptionTerm
  Identity -> toIdentityTerm

getBindOperator :: ConversionMonad -> G.Term
getBindOperator (Option  ) = optionBindOperator
getBindOperator (Identity) = identityBindOperator

-- Convert Terms Monadic
toOptionTerm :: G.Term -> G.Term
toOptionTerm term = G.App optionTerm (singleton (G.PosArg term))

toIdentityTerm :: G.Term -> G.Term
toIdentityTerm term = G.App identityTerm (singleton (G.PosArg term))

toReturnTerm :: G.Term -> ConversionMonad -> G.Term
toReturnTerm term (Option) = G.App optionReturnTerm (singleton (G.PosArg term))
toReturnTerm term (Identity) =
  G.App identityReturnTerm (singleton (G.PosArg term))

---------------------- Add Monadic Prefixes
addMonadicPrefix :: String -> G.Name -> G.Name
addMonadicPrefix str (G.Ident (G.Bare ident)) = G.Ident
  (strToQId (str ++ name))
  where name = T.unpack ident

addMonadicPrefixToBinder :: ConversionMonad -> G.Binder -> G.Binder
addMonadicPrefixToBinder m (G.Inferred expl name) =
  G.Inferred expl (getPrefixFromMonad m name)
addMonadicPrefixToBinder m (G.Typed gen expl (name B.:| xs) ty) =
  if isArrowTerm ty
    then G.Typed gen expl (name B.:| xs) ty
    else G.Typed gen expl (singleton (getPrefixFromMonad m name)) ty

addMonadicPrefixToQId :: ConversionMonad -> G.Qualid -> G.Qualid
addMonadicPrefixToQId m qId = gNameToQId (getPrefixFromMonad m (G.Ident qId))

getPrefixFromMonad :: ConversionMonad -> (G.Name -> G.Name)
getPrefixFromMonad Option   = addOptionPrefix
getPrefixFromMonad Identity = addIdentityPrefix

-- Monadic Prefixes used
addOptionPrefix :: G.Name -> G.Name
addOptionPrefix = addMonadicPrefix "o"

addIdentityPrefix :: G.Name -> G.Name
addIdentityPrefix = addMonadicPrefix "i"
  ---------------------- Remove Monadic Elements

removeMonadFromBinder :: G.Binder -> G.Binder
removeMonadFromBinder (G.Typed gen expl (n B.:| _) term) =
  G.Typed gen expl (singleton (removeMonadicPrefix n)) (fromMonadicTerm term)

removeMonadicPrefix :: G.Name -> G.Name
removeMonadicPrefix name = strToGName (tail (getStringFromGName name))

fromMonadicTerm :: G.Term -> G.Term
fromMonadicTerm (G.App _ (G.PosArg term B.:| _)) = term
fromMonadicTerm term                             = term

---------------------- Bool Functions
isPatName :: G.Term -> [G.Qualid] -> Bool
isPatName (G.Qualid qId) qIds = any (eqQId qId) qIds
isPatName _              _    = False

isMonadicTerm :: G.Term -> Bool
isMonadicTerm (G.App term _) = isMonad term
isMonadicTerm _              = False

isMonad :: G.Term -> Bool
isMonad (G.Qualid qId) = any
  (eqQId qId)
  (map
    strToQId
    [ "option"
    , "identity"
    , "o_return"
    , "i_return"
    , "op_>>=__"
    , "op_>>='__"
    , "o_bind"
    , "i_bind"
    ]
  )
isMonad _ = False

predefinedMonadicFunctions :: [G.Qualid]
predefinedMonadicFunctions = map strToQId ["singleton"]

isMonadicFunctionCall :: G.Term -> [TypeSignature] -> Bool
isMonadicFunctionCall (G.Qualid qId) typeSigs =
  isJust maybeTypeSig
    || isJust maybeHelperFun
    || any (eqQId qId) predefinedMonadicFunctions
    || eqQId qId (termToQId optionBindOperator)
    || eqQId qId (termToQId identityBindOperator)
 where
  maybeTypeSig = getTypeSignatureByQId typeSigs qId
  maybeHelperFun =
    getTypeSignatureByQId typeSigs (strToQId (qIdToStr qId ++ "'"))
isMonadicFunctionCall (G.App term _) typeSig =
  isMonadicFunctionCall term typeSig
isMonadicFunctionCall _ _ = False

isMonadicBinder :: G.Term -> [G.Binder] -> Bool
isMonadicBinder (G.Qualid qId) binders = isJust maybeBinder
  && isMonadicTerm (getBinderType (fromJust maybeBinder))
  where maybeBinder = getBinderByQId binders qId
isMonadicBinder _ _ = False

isMonadicArrowTerm :: G.Term -> [G.Binder] -> Bool
isMonadicArrowTerm (G.Qualid qId) binders = isJust maybeBinder
  && isArrowTerm (getBinderType (fromJust maybeBinder))
  where maybeBinder = getBinderByQId binders qId
isMonadicArrowTerm _ _ = False

errorEquation :: ConversionMonad -> [G.Equation]
errorEquation (Option) =
  [ G.Equation (singleton (G.MultPattern (singleton G.UnderscorePat)))
               (G.Qualid (strToQId "None"))
  ]
errorEquation (Identity) =
  [ G.Equation (singleton (G.MultPattern (singleton G.UnderscorePat)))
               (G.Qualid (strToQId "error"))
  ]

---------------------- Predefined Terms
identityTerm :: G.Term
identityTerm = G.Qualid (strToQId "identity")

optionTerm :: G.Term
optionTerm = G.Qualid (strToQId "option")

singletonTerm :: G.Term
singletonTerm = G.Qualid (strToQId "singleton")

optionReturnTerm :: G.Term
optionReturnTerm = G.Qualid (strToQId "o_return")

identityReturnTerm :: G.Term
identityReturnTerm = G.Qualid (strToQId "i_return")

optionBindOperator :: G.Term
optionBindOperator = G.Qualid (strToQId "op_>>=__")

identityBindOperator :: G.Term
identityBindOperator = G.Qualid (strToQId "op_>>='__")
