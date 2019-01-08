module Compiler.MonadicConverter where

import Language.Coq.Gallina as G

import Compiler.Types
import Compiler.HelperFunctions

import qualified Data.Text as T
import qualified GHC.Base as B
import Data.Maybe

---------------------- Add Bind Operator to Definition
addBindOperatorsToDefinition :: [G.Binder] -> G.Term -> G.Term
addBindOperatorsToDefinition [] term =
  if isMonadicTerm term
    then term
    else toReturnTerm term
addBindOperatorsToDefinition (x : xs) term =
  G.App bindOperator
    (toNonemptyList [G.PosArg argumentName, G.PosArg lambdaFun])
  where
    argumentName = getBinderName x
    lambdaFun = G.Fun (singleton $ removeMonadFromBinder x) (addBindOperatorsToDefinition xs term )

---------------------- Add Return Operator if rhs isn't already monadic
addReturnToMatch :: G.Term -> [G.TypeSignature] -> [G.Binder] -> G.Term
addReturnToMatch (G.Match mItem retType equations) typeSigs binders =
  G.Match mItem retType [addReturnToEquation e typeSigs binders | e <- equations]

addReturnToEquation :: G.Equation -> [G.TypeSignature] -> [G.Binder] -> G.Equation
addReturnToEquation (G.Equation multPats rhs) typeSigs binders =
  G.Equation multPats (addReturnToRhs rhs typeSigs binders)

addReturnToRhs :: G.Term -> [G.TypeSignature] -> [G.Binder] -> G.Term
addReturnToRhs (G.App constr args) typeSigs binders =
  if isMonadicTerm constr || isMonadicFunctionCall constr typeSigs || isMonadicBinder constr binders
    then G.App constr args
    else toReturnTerm $ G.App constr args
addReturnToRhs (G.Parens term) typeSigs binders =
  G.Parens $ addReturnToRhs term typeSigs binders
addReturnToRhs term typeSigs binders =
  if isMonadicTerm term || isMonadicFunctionCall term typeSigs || isMonadicBinder term binders
    then term
    else toReturnTerm term

---------------------- transform Data Structures Monadic
transformBindersMonadic :: [G.Binder] -> ConversionMonad -> [G.Binder]
transformBindersMonadic binders m =
  [transformBinderMonadic (addMonadicPrefixToBinder m b) m | b <- binders]

transformBinderMonadic :: G.Binder -> ConversionMonad -> G.Binder
transformBinderMonadic (G.Typed gen expl name term) m =
  G.Typed gen expl name (transformTermMonadic term m)

transformTermMonadic :: G.Term -> ConversionMonad -> G.Term
transformTermMonadic (G.Sort G.Type) m =
  typeTerm
transformTermMonadic term m =
  monad term
  where
    monad = case m of
          Option -> toOptionTerm
          Identity -> toIdentityTerm

-- Convert Terms Monadic
toOptionTerm :: G.Term -> G.Term
toOptionTerm term =
  G.App optionTerm (singleton (G.PosArg term))

toIdentityTerm :: G.Term -> G.Term
toIdentityTerm term =
  G.App identityTerm (singleton (G.PosArg term))

toReturnTerm :: G.Term -> G.Term
toReturnTerm term =
  G.App returnTerm (singleton (G.PosArg (G.Parens term)))

---------------------- Add Monadic Prefixes

addMonadicPrefix :: String -> G.Name -> G.Name
addMonadicPrefix str (G.Ident (G.Bare ident)) =
  G.Ident (strToQId (str ++ name))
  where
    name = T.unpack ident

addMonadicPrefixToBinder ::  ConversionMonad -> G.Binder -> G.Binder
addMonadicPrefixToBinder m (G.Inferred expl name) =
  G.Inferred expl (getPrefixFromMonad m name)
addMonadicPrefixToBinder m (G.Typed gen expl (name B.:| xs) ty) =
  G.Typed gen expl (singleton (getPrefixFromMonad m name)) ty

addMonadicPrefixToQId ::  ConversionMonad -> G.Qualid -> G.Qualid
addMonadicPrefixToQId m qId =
  gNameToQId (getPrefixFromMonad m (G.Ident qId))


getPrefixFromMonad :: ConversionMonad -> (G.Name -> G.Name)
getPrefixFromMonad Option = addOptionPrefix
getPrefixFromMonad Identity = addIdentityPrefix

-- Monadic Prefixes used
addOptionPrefix :: G.Name -> G.Name
addOptionPrefix =
  addMonadicPrefix "o"

addIdentityPrefix :: G.Name -> G.Name
addIdentityPrefix =
  addMonadicPrefix "i"

  ---------------------- Remove Monadic Elements

removeMonadFromBinder :: G.Binder -> G.Binder
removeMonadFromBinder (G.Typed gen expl (n B.:| xs) term) =
  G.Typed gen expl (singleton (removeMonadicPrefix n)) (fromMonadicTerm term)

removeMonadicPrefix :: G.Name -> G.Name
removeMonadicPrefix name =
  strToGName (tail (getStringFromGName name))

fromMonadicTerm :: G.Term -> G.Term
fromMonadicTerm (G.App _ (G.PosArg term B.:| xs)) =
  term
fromMonadicTerm term =
  term
---------------------- Bool Functions
isMonadicTerm :: G.Term -> Bool
isMonadicTerm (G.App term _ ) =
  isMonad term
isMonadicTerm term =
  False

isMonad :: G.Term -> Bool
isMonad (G.Qualid qId) =
  any (eqQId qId) $ map strToQId ["option", "identity", "return_"]

isMonadicFunctionCall :: G.Term -> [G.TypeSignature] -> Bool
isMonadicFunctionCall (G.Qualid qId) typeSigs =
  isJust maybeTypeSig
  where maybeTypeSig = getTypeSignatureByQId typeSigs qId

isMonadicBinder :: G.Term -> [G.Binder] -> Bool
isMonadicBinder (G.Qualid qId) binders =
  isJust maybeBinder && isMonadicTerm (getBinderType (fromJust maybeBinder))
  where maybeBinder = getBinderByQId binders qId
---------------------- Predefined Terms
identityTerm :: G.Term
identityTerm =
  G.Qualid (strToQId "identity")

optionTerm :: G.Term
optionTerm =
  G.Qualid (strToQId "option")

returnTerm :: G.Term
returnTerm =
  G.Qualid (strToQId "return_")

bindOperator :: G.Term
bindOperator =
  G.Qualid (strToQId "op_>>=__")
