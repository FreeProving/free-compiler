module Compiler.FueledFunctions where

import Compiler.HelperFunctions
import Compiler.MonadicConverter (addReturnToMatch,
                                  addReturnToArgs)

import Language.Coq.Gallina as G
import Language.Haskell.Exts.Syntax

import qualified GHC.Base as B

---------------------- Transform to fueled function
addFuelArgumentToRecursiveCall :: G.Term -> G.Qualid -> G.Term
addFuelArgumentToRecursiveCall (G.App term args) funName =
  if containsRecursiveCall term funName
    then G.App term (addDecrFuelArgument args)
    else G.App term (toNonemptyList checkedArgList)
  where
    termList = convertArgumentsToTerms (nonEmptyListToList args)
    checkedArgList = convertTermsToArguments [addFuelArgumentToRecursiveCall t funName | t <- termList]
addFuelArgumentToRecursiveCall (G.Parens term) funName =
  G.Parens (addFuelArgumentToRecursiveCall term funName)
addFuelArgumentToRecursiveCall term _ =
  term

addFuelMatching :: G.Term -> G.Qualid -> G.Term
addFuelMatching  =
  fuelPattern (G.Qualid (strToQId "None"))

convertFueledFunBody :: G.Term -> [G.Binder] -> G.Qualid -> [G.TypeSignature] -> G.Term
convertFueledFunBody (G.Match item rType equations) funBinders funName typeSigs =
  addReturnToMatch (G.Match item rType [convertFueledEquation e funBinders funName typeSigs | e <- equations]) typeSigs funBinders

convertFueledEquation ::  G.Equation -> [G.Binder] -> G.Qualid -> [G.TypeSignature] -> G.Equation
convertFueledEquation (G.Equation multPats rhs) funBinders funName typeSigs =
  G.Equation multPats (convertFueledTerm rhs funBinders funName typeSigs)

convertFueledTerm :: G.Term -> [G.Binder] -> G.Qualid -> [G.TypeSignature] -> G.Term
convertFueledTerm (G.Match item rType equations) funBinders funName typeSigs =
  convertFueledFunBody (G.Match item rType equations) funBinders funName typeSigs
convertFueledTerm (G.Parens term) funBinders funName typeSigs =
  G.Parens $ convertFueledTerm term funBinders funName typeSigs
convertFueledTerm (G.Qualid qId) funBinders funName typeSigs =
  G.Qualid qId
convertFueledTerm (G.App constr args) funBinders funName typeSigs =
  if isQualidTerm constr
    then if containsRecursiveCall constr funName || isRecursiveFunction constr typeSigs
            then G.App constr convertedFueledArgs
            else G.App constr (toNonemptyList convertedArgs)
    else G.App (convertFueledTerm constr funBinders funName typeSigs) (toNonemptyList convertedArgs)
  where convertedArgs = convertTermsToArguments [convertFueledTerm t funBinders funName typeSigs |
                          t <- convertArgumentsToTerms (nonEmptyListToList args)]
        fixedArguments = addReturnToArgs convertedArgs typeSigs funBinders
        convertedFueledArgs = addDecrFuelArgument (toNonemptyList fixedArguments)


addDecrFuelArgument :: B.NonEmpty G.Arg -> B.NonEmpty G.Arg
addDecrFuelArgument list =
  toNonemptyList (G.PosArg decrFuelTerm : nonEmptyListToList list)

addFuelBinder :: [G.Binder] -> [G.Binder]
addFuelBinder binders = fuelBinder : binders


---------------------- Pattern Matching over fuel Argument
fuelPattern :: G.Term -> G.Term -> G.Qualid -> G.Term
fuelPattern errorTerm recursiveCall funName =
  G.Match (singleton (G.MatchItem name Nothing Nothing)) Nothing equations
  where
    name = strToTerm "fuel"
    equations = [zeroCase, nonZeroCase]
    zeroCase = G.Equation (singleton (G.MultPattern (singleton (G.QualidPat (strToQId "O"))))) errorTerm
    nonZeroCase = G.Equation (singleton (G.MultPattern (singleton (G.ArgsPat (strToQId "S") [G.QualidPat decrFuel])))) recursiveCallWithFuel
    decrFuel = strToQId "rFuel"
    recursiveCallWithFuel = addFuelArgumentToRecursiveCall recursiveCall funName

---------------------- Predefined Terms
decrFuelTerm :: G.Term
decrFuelTerm =
  G.Qualid (strToQId "rFuel")

fuelBinder :: G.Binder
fuelBinder =
  G.Typed G.Ungeneralizable G.Explicit fuelName natTerm
  where
    natTerm = G.Qualid (strToQId "nat")
    fuelName = singleton (strToGName "fuel")
