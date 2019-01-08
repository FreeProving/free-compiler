module Compiler.FueledFunctions where

import Compiler.HelperFunctions

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
  G.Match item rType [convertFueledEquation e funBinders funName typeSigs | e <- equations]

convertFueledEquation ::  G.Equation -> [G.Binder] -> G.Qualid -> [G.TypeSignature] -> G.Equation
convertFueledEquation (G.Equation multPats rhs) funBinders funName typeSigs =
  G.Equation multPats (convertFueledRhs rhs funBinders funName typeSigs)

convertFueledRhs :: G.Term -> [G.Binder] -> G.Qualid -> [G.TypeSignature] -> G.Term
convertFueledRhs term funBinders funName typeSigs =
  term -- placeholder

addFuelMatchingToRhs :: G.Term -> [G.Binder] -> [G.Binder] -> G.Qualid -> G.Term -> G.Term
addFuelMatchingToRhs (G.Match item rType equations) funBinders lambdaBinders funName retType =
  G.Match item rType [addFuelMatchingToEquation e funBinders lambdaBinders funName retType | e <- equations]
addFuelMatchingToRhs term funBinders lambdaBinders funName retType =
  if containsRecursiveCall term funName
    then fuelPattern errorTerm recursiveCall funName
    else case term of
      G.App returnOp (b B.:| []) -> G.App returnOp (singleton $ G.PosArg (addFuelMatchingToRhs
                                                                  ((\(G.PosArg x) -> x ) b)
                                                                    funBinders
                                                                      lambdaBinders
                                                                        funName
                                                                          retType))
      G.App bindOp (b B.:| bs) -> G.App bindOp (toNonemptyList [b,
                                        G.PosArg (addFuelMatchingToRhs
                                          ((\(G.PosArg x) -> x ) (head bs))
                                            funBinders
                                              lambdaBinders
                                                funName
                                                  retType)])
      G.Fun lBinders rhs -> G.Fun lBinders (addFuelMatchingToRhs
                                            rhs
                                              funBinders
                                                (lambdaBinders ++ [head (nonEmptyListToList lBinders)])
                                                  funName
                                                    retType)
      G.Parens term -> G.Parens $ addFuelMatchingToRhs
                                    term
                                      funBinders
                                        lambdaBinders
                                          funName
                                            retType
      term -> term
  where
    errorTerm = getBinderName $ findFittingBinder lambdaBinders retType
    recursiveCall = fixRecursiveCallArguments term funBinders lambdaBinders funName

addFuelMatchingToEquation :: G.Equation -> [G.Binder] -> [G.Binder] -> G.Qualid -> G.Term -> G.Equation
addFuelMatchingToEquation (G.Equation multPattern rhs) funBinders lambdaBinders funName retType =
  G.Equation multPattern (addFuelMatchingToRhs rhs funBinders lambdaBinders funName retType)

addDecrFuelArgument :: B.NonEmpty G.Arg -> B.NonEmpty G.Arg
addDecrFuelArgument list =
  toNonemptyList (nonEmptyListToList list ++ [G.PosArg decrFuelTerm] )

addFuelBinder :: [G.Binder] -> [G.Binder]
addFuelBinder binders = fuelBinder : binders

fixRecursiveCallArguments :: G.Term -> [G.Binder] -> [G.Binder] -> G.Qualid -> G.Term
fixRecursiveCallArguments (G.App term args) funBinders lambdaBinders funName =
  if containsRecursiveCall term funName
    then G.App term (toNonemptyList matchingArgs)
    else G.App term (toNonemptyList (convertTermsToArguments [fixRecursiveCallArguments t funBinders lambdaBinders funName | t <- terms]))
    where
      terms = convertArgumentsToTerms (nonEmptyListToList args)
      matchingArgs = compAndChangeArguments (nonEmptyListToList args) funBinders lambdaBinders
fixRecursiveCallArguments (G.Parens term) funBinders lambdaBinders funName =
  G.Parens (fixRecursiveCallArguments term funBinders lambdaBinders funName)
fixRecursiveCallArguments term _ _ _ = term

compAndChangeArguments :: [G.Arg] -> [G.Binder] -> [G.Binder] -> [G.Arg]
compAndChangeArguments [] _ _ = []
compAndChangeArguments (x : xs) funBinders lambdaBinders =
  if containsWrongArgument x lambdaBinders
    then rightArg : compAndChangeArguments xs funBinders lambdaBinders
    else x : compAndChangeArguments xs funBinders lambdaBinders
    where
      rightArg = switchArgument (length xs) funBinders

containsWrongArgument :: G.Arg -> [G.Binder] -> Bool
containsWrongArgument (G.PosArg (G.Qualid qId)) =
  any (qIdEqBinder qId)

switchArgument :: Int -> [G.Binder] -> G.Arg
switchArgument n funBinders =
  binderToArg bind
  where
    bind = funBinders !! (length funBinders - n - 1)



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
