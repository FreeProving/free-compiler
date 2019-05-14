module Compiler.HelperFunctions where

import qualified Language.Coq.Gallina as G
import qualified Language.Haskell.Exts.Syntax as H

import qualified Data.Text as T

import Data.List (nub)
import Data.Maybe (isJust)
import qualified GHC.Base as B

import Compiler.NonEmptyList (fromNonEmptyList, singleton, toNonemptyList)

---------------------- Getter Functions
--Get Strings From Data Structures
getQString :: Show l => H.QName l -> String
getQString (H.UnQual _ name) = getString name
getQString (H.Special _ specCon) = T.unpack (specConToText specCon)

getString :: Show l => H.Name l -> String
getString (H.Ident _ str) = str
getString (H.Symbol _ str) = str

getStringFromGName :: G.Name -> String
getStringFromGName (G.Ident qId) = getStringFromQId qId
getStringFromGName G.UnderscoreName = "_"

getStringFromQId :: G.Qualid -> String
getStringFromQId (G.Bare text) = T.unpack text

--manual covnversion of common Haskell types to coq equivalent
getType :: String -> G.Term
getType "Int" = strToTerm "nat"
getType "Bool" = strToTerm "bool"
getType "String" = strToTerm "string"
getType str = strToTerm str

getConstr :: String -> G.Term
getConstr "unit" = strToTerm "tt"
getConstr "True" = strToTerm "true"
getConstr "False" = strToTerm "false"
getConstr str = strToTerm str

getTypeSignatureByName :: Show l => [G.TypeSignature] -> H.Name l -> Maybe G.TypeSignature
getTypeSignatureByName [] name = Nothing
getTypeSignatureByName (x:xs) name =
  if typeNameEqName x name
    then Just x
    else getTypeSignatureByName xs name

getTypeSignatureByQId :: [G.TypeSignature] -> G.Qualid -> Maybe G.TypeSignature
getTypeSignatureByQId [] _ = Nothing
getTypeSignatureByQId (x:xs) qId =
  if typeNameEqQId x qId
    then Just x
    else getTypeSignatureByQId xs qId

getMatchFromTerm :: G.Term -> G.Term
getMatchFromTerm (G.Match mItem retType equations) = G.Match mItem retType equations
getMatchFromTerm (G.App cons args) =
  if containsMatchTerm cons
    then getMatchFromTerm cons
    else getMatchFromTerm (head (filter containsMatchTerm (map argToTerm (fromNonEmptyList args))))
getMatchFromTerm (G.If _ cond _ tTerm eTerm) =
  if containsMatchTerm cond
    then getMatchFromTerm cond
    else if containsMatchTerm tTerm
           then getMatchFromTerm tTerm
           else getMatchFromTerm eTerm

getMatchItem :: G.Term -> G.MatchItem
getMatchItem (G.Match mItem _ _) = (head . fromNonEmptyList) mItem

getTermFromMatchItem :: G.MatchItem -> G.Term
getTermFromMatchItem (G.MatchItem term _ _) = term

getConstrNamesFromDataDecls :: Show l => [H.Decl l] -> [[(G.Qualid, Maybe G.Qualid)]]
getConstrNamesFromDataDecls sentences = [getConstrNamesFromDataDecl s sentences | s <- sentences]

getNamesFromDataDecls :: Show l => [H.Decl l] -> [G.Name]
getNamesFromDataDecls sentences = [getNameFromDataDecl s | s <- sentences]

getConstrNamesFromDataDecl :: Show l => H.Decl l -> [H.Decl l] -> [(G.Qualid, Maybe G.Qualid)]
getConstrNamesFromDataDecl (H.DataDecl _ _ _ declHead cons _) _ =
  [getConstrNameFromQConDecl c (getNameFromDeclHead declHead) | c <- cons]
getConstrNamesFromDataDecl (H.TypeDecl _ _ ty) sentences = getConstrsByName (typeToGName ty) sentences

getConstrsByName :: Show l => G.Name -> [H.Decl l] -> [(G.Qualid, Maybe G.Qualid)]
getConstrsByName name (H.DataDecl _ _ _ declHead cons _:xs) =
  if eqGName name (getNameFromDeclHead declHead)
    then [getConstrNameFromQConDecl c (getNameFromDeclHead declHead) | c <- cons]
    else getConstrsByName name xs
getConstrsByName name (_:xs) = getConstrsByName name xs
getConstrsByName name [] = error (show name)

getConstrsByPattern :: G.Pattern -> [[G.Qualid]] -> Maybe [G.Qualid]
getConstrsByPattern G.UnderscorePat _ = Nothing
getConstrsByPattern (G.QualidPat qId) dataTypeConstrs =
  if (not . null) filteredConstrs
    then Just (head filteredConstrs)
    else Nothing
  where
    filteredConstrs = filter (not . null) (map (getConstrSet qId) dataTypeConstrs)
getConstrsByPattern (G.ArgsPat qId _) dataTypeConstrs =
  if (not . null) filteredConstrs
    then Just (head filteredConstrs)
    else Nothing
  where
    filteredConstrs = filter (not . null) (map (getConstrSet qId) dataTypeConstrs)

getConstrSet :: G.Qualid -> [G.Qualid] -> [G.Qualid]
getConstrSet qId constrs =
  if any (eqQId qId) constrs
    then constrs
    else []

getConstrNameFromQConDecl :: Show l => H.QualConDecl l -> G.Name -> (G.Qualid, Maybe G.Qualid)
getConstrNameFromQConDecl (H.QualConDecl _ _ _ (H.ConDecl _ conName _)) funName =
  if gNameToStr funName == conStr
    then (strToQId (conStr ++ "_"), Just (strToQId conStr))
    else (strToQId conStr, Nothing)
  where
    conStr = nameToStr conName

getNameFromDataDecl :: Show l => H.Decl l -> G.Name
getNameFromDataDecl (H.DataDecl _ _ _ declHead _ _) = getNameFromDeclHead declHead
getNameFromDataDecl (H.TypeDecl _ declHead _) = getNameFromDeclHead declHead

getNameFromDeclHead :: Show l => H.DeclHead l -> G.Name
getNameFromDeclHead (H.DHead _ name) = nameToGName name
getNameFromDeclHead (H.DHParen _ declHead) = getNameFromDeclHead declHead
getNameFromDeclHead (H.DHApp _ declHead _) = getNameFromDeclHead declHead

getReturnTypeFromDeclHead :: [G.Arg] -> G.Qualid -> G.Term
getReturnTypeFromDeclHead [] qId = G.Qualid qId
getReturnTypeFromDeclHead (x:xs) qId = G.App (G.Qualid qId) (x B.:| xs)

getConstrNames :: Show l => [H.QualConDecl l] -> [G.Qualid]
getConstrNames qConDecls = [getNameFromQualConDecl d | d <- qConDecls]

getNameFromQualConDecl :: Show l => H.QualConDecl l -> G.Qualid
getNameFromQualConDecl (H.QualConDecl _ _ _ (H.ConDecl _ name _)) = nameToQId name

getTypeNamesFromTerm :: G.Term -> [G.Name]
getTypeNamesFromTerm (G.App term args) =
  map strToGName (termToStrings term) ++ map strToGName (concatMap (termToStrings . argToTerm) (fromNonEmptyList args))
getTypeNamesFromTerm (G.Parens term) = getTypeNamesFromTerm term
getTypeNamesFromTerm (G.Arrow lTerm rTerm) =
  map strToGName (termToStrings lTerm) ++ map strToGName (termToStrings rTerm)
getTypeNamesFromTerm _ = []

getConstrNameFromType :: G.Term -> G.Name
getConstrNameFromType (G.App term _) = head (map strToGName (termToStrings term))
getConstrNameFromType _ = strToGName ""

getReturnType :: G.TypeSignature -> G.Term
getReturnType (G.TypeSignature _ terms) = last terms

getBinderName :: G.Binder -> G.Term
getBinderName (G.Inferred _ name) = gNameToTerm name
getBinderName (G.Typed _ _ (name B.:| xs) _) = gNameToTerm name

getBinderType :: G.Binder -> G.Term
getBinderType (G.Typed _ _ _ term) = term
getBinderType (G.Inferred _ _) = typeTerm

getBinderByQId :: [G.Binder] -> G.Qualid -> Maybe G.Binder
getBinderByQId [] _ = Nothing
getBinderByQId (x:xs) qId =
  if eqQId qId (termToQId (getBinderName x))
    then Just x
    else getBinderByQId xs qId

getPatternFromMultPattern :: G.MultPattern -> [G.Pattern]
getPatternFromMultPattern (G.MultPattern pats) = fromNonEmptyList pats

getQIdsFromPattern :: G.Pattern -> [G.Qualid]
getQIdsFromPattern (G.ArgsPat _ pats) = concatMap getQIdsFromPattern pats
getQIdsFromPattern (G.QualidPat qId) = [qId]
getQIdsFromPattern pat = []

getQIdFromPattern :: G.Pattern -> G.Qualid
getQIdFromPattern (G.ArgsPat qId _) = qId
getQIdFromPattern (G.QualidPat qId) = qId
getQIdFromPattern (G.InfixPat _ op _) = G.Bare op
getQIdFromPattern G.UnderscorePat = strToQId "_"

getRhsFromEquation :: G.Equation -> G.Term
getRhsFromEquation (G.Equation _ term) = term

getPatternFromEquation :: G.Equation -> [G.Pattern]
getPatternFromEquation (G.Equation multPats _) = (getPatternFromMultPattern . head . fromNonEmptyList) multPats

---------------------- Bool Functions
isSpecialConstr :: Show l => H.QName l -> Bool
isSpecialConstr (H.Special _ _) = True
isSpecialConstr _ = False

isSpecialOperator :: Show l => H.QOp l -> Bool
isSpecialOperator (H.QVarOp _ qName) = isSpecialConstr qName
isSpecialOperator (H.QConOp _ qName) = isSpecialConstr qName

isCoqType :: G.Name -> Bool
isCoqType name = not (any (eqGName name) coqTypes)

isTypeSig :: Show l => H.Decl l -> Bool
isTypeSig H.TypeSig {} = True
isTypeSig _ = False

isDataDecl :: Show l => H.Decl l -> Bool
isDataDecl H.DataDecl {} = True
isDataDecl H.TypeDecl {} = True
isDataDecl _ = False

hasNonInferrableConstr :: Show l => [H.QualConDecl l] -> Bool
hasNonInferrableConstr constrs = any isNonInferrableConstr constrs || length constrs > 1

isNonInferrableConstr :: Show l => H.QualConDecl l -> Bool
isNonInferrableConstr (H.QualConDecl _ _ _ (H.ConDecl _ _ [])) = True
isNonInferrableConstr _ = False

isUnderscorePat :: G.Pattern -> Bool
isUnderscorePat G.UnderscorePat = True
isUnderscorePat _ = False

containsAllConstrs :: [G.Pattern] -> [G.Qualid] -> Bool
containsAllConstrs [] constrs = null constrs
containsAllConstrs (p:ps) constrs = containsAllConstrs ps (filter (not . eqQId constrQId) constrs)
  where
    constrQId = getQIdFromPattern p

containsRecursiveCall :: G.Term -> G.Qualid -> Bool
containsRecursiveCall (G.Match _ _ equations) funName =
  or [containsRecursiveCall t funName | t <- map getRhsFromEquation equations]
containsRecursiveCall (G.App term args) funName =
  containsRecursiveCall term funName || or [containsRecursiveCall t funName | t <- argTerms]
  where
    argTerms = convertArgumentsToTerms (fromNonEmptyList args)
containsRecursiveCall (G.Parens term) funName = containsRecursiveCall term funName
containsRecursiveCall (G.Qualid qId) funName = eqQId qId funName
containsRecursiveCall (G.If _ cond _ thenTerm elseTerm) funName =
  containsRecursiveCall cond funName || containsRecursiveCall thenTerm funName || containsRecursiveCall elseTerm funName
containsRecursiveCall _ _ = False

isFunctionCall :: G.Term -> [G.TypeSignature] -> Bool
isFunctionCall (G.Qualid qId) typeSigs = isJust (getTypeSignatureByQId typeSigs qId)

containsMatchTerm :: G.Term -> Bool
containsMatchTerm (G.Parens term) = containsMatchTerm term
containsMatchTerm (G.App term args) =
  containsMatchTerm term || any containsMatchTerm (map argToTerm (fromNonEmptyList args))
containsMatchTerm (G.If _ term _ tTerm eTerm) =
  containsMatchTerm term || containsMatchTerm tTerm || containsMatchTerm eTerm
containsMatchTerm (G.Fun _ term) = containsMatchTerm term
containsMatchTerm (G.Match _ _ _) = True
containsMatchTerm _ = False

isAppTerm :: G.Term -> Bool
isAppTerm (G.App _ _) = True
isAppTerm _ = False

isArrowTerm :: G.Term -> Bool
isArrowTerm (G.Parens term) = isArrowTerm term
isArrowTerm (G.Arrow _ _) = True
isArrowTerm _ = False

isQualidTerm :: G.Term -> Bool
isQualidTerm (G.Qualid _) = True
isQualidTerm _ = False

-- name comparison functions
gNameEqName :: Show l => G.Name -> H.Name l -> Bool
gNameEqName (G.Ident (G.Bare gName)) (H.Ident _ name) = T.unpack gName == name

eqGName :: G.Name -> G.Name -> Bool
eqGName gNameL gNameR = getStringFromGName gNameL == getStringFromGName gNameR

eqQId :: G.Qualid -> G.Qualid -> Bool
eqQId qIdL qIdR = getStringFromQId qIdL == getStringFromQId qIdR

eqBinder :: G.Binder -> G.Binder -> Bool
eqBinder lBinder rBinder = eqQId ((termToQId . getBinderName) lBinder) ((termToQId . getBinderName) rBinder)

qIdEqBinder :: G.Qualid -> G.Binder -> Bool
qIdEqBinder qId (G.Typed _ _ (n B.:| _) _) = eqQId qId (gNameToQId n)
qIdEqBinder qId (G.Inferred _ n) = eqQId qId (gNameToQId n)

dataTypeUneqGName :: G.Name -> G.Name -> Bool
dataTypeUneqGName dataType gName = nameString /= dataString
  where
    dataString = getStringFromGName dataType
    nameString = getStringFromGName gName

typeNameEqName :: Show l => G.TypeSignature -> H.Name l -> Bool
typeNameEqName (G.TypeSignature sigName _) = gNameEqName sigName

typeNameEqQId :: G.TypeSignature -> G.Qualid -> Bool
typeNameEqQId (G.TypeSignature sigName _) = eqQId (gNameToQId sigName)

---------------------- various helper functions
changeSimilarType :: G.Qualid -> G.Qualid
changeSimilarType qId =
  if any (eqQId qId) haskellTypes
    then strToQId (qIdToStr qId ++ "_")
    else qId

typeToGName :: Show l => H.Type l -> G.Name
typeToGName (H.TyCon _ name) = qNameToGName name
typeToGName (H.TyApp _ constr _) = typeToGName constr
typeToGName (H.TyList _ _) = strToGName "List"
typeToGName H.TyTuple {} = strToGName "Pair"
typeToGName ty = error "type not implemented"

filterEachElement :: [a] -> (a -> a -> Bool) -> [a] -> [a]
filterEachElement [] f list = list
filterEachElement (x:xs) f list = filterEachElement xs f filteredList
  where
    filteredList = filter (f x) list

--return Binder that fits a certain Type Signature
findFittingBinder :: [G.Binder] -> G.Term -> G.Binder
findFittingBinder binders ty = head (filter (\x -> ty == getBinderType x) binders)

addInferredTypesToSignature :: [G.Binder] -> [G.Name] -> G.Term -> [G.Binder]
addInferredTypesToSignature binders dataNames retType =
  if null filteredTypeNames
    then binders
    else G.Typed G.Ungeneralizable G.Explicit (toNonemptyList filteredTypeNames) typeTerm : binders
  where
    filteredTypeNames = nub (filterEachElement dataNames dataTypeUneqGName (filter isCoqType typeNames))
    typeNames = concatMap getTypeNamesFromTerm typeTerms
    typeTerms = (retType : map getBinderType binders)
    consNames = nub (map getConstrNameFromType typeTerms)

getInferredBindersFromRetType :: G.Term -> [G.Binder]
getInferredBindersFromRetType (G.App constr args) =
  concatMap getInferredBindersFromRetType (convertArgumentsToTerms (fromNonEmptyList args))
getInferredBindersFromRetType (G.Qualid qId) =
  [G.Typed G.Ungeneralizable G.Explicit (singleton (qIdToGName qId)) typeTerm]

convertArgumentsToTerms :: [G.Arg] -> [G.Term]
convertArgumentsToTerms = map argToTerm

convertTermsToArguments :: [G.Term] -> [G.Arg]
convertTermsToArguments = map G.PosArg

collapseApp :: G.Term -> G.Term
collapseApp (G.App term args) =
  if isAppTerm term
    then G.App funName (toNonemptyList combinedArgs)
    else G.App term args
  where
    funName = returnAppName term
    combinedArgs = combineArgs (fromNonEmptyList args) term
collapseApp (G.Parens term) = G.Parens (collapseApp term)
collapseApp term = term

returnAppName :: G.Term -> G.Term
returnAppName (G.App term _) = returnAppName term
returnAppName term = term

combineArgs :: [G.Arg] -> G.Term -> [G.Arg]
combineArgs args (G.App term args') = combineArgs combArgs term
  where
    combArgs = fromNonEmptyList args' ++ args
combineArgs args _ = convertTermsToArguments (map collapseApp (convertArgumentsToTerms args))

--apply a function only to the actual head of a DeclHead
applyToDeclHead :: Show l => H.DeclHead l -> (H.Name l -> a) -> a
applyToDeclHead (H.DHead _ name) f = f name
applyToDeclHead (H.DHApp _ declHead _) f = applyToDeclHead declHead f

--apply a function to every tyVarBind of a DeclHead and reverse it (to get arguments in right order)
applyToDeclHeadTyVarBinds :: Show l => H.DeclHead l -> (H.TyVarBind l -> a) -> [a]
applyToDeclHeadTyVarBinds (H.DHead _ _) f = []
applyToDeclHeadTyVarBinds (H.DHApp _ declHead tyVarBind) f =
  reverse (f tyVarBind : reverse (applyToDeclHeadTyVarBinds declHead f))

toGallinaSyntax :: String -> String
toGallinaSyntax "False" = "false"
toGallinaSyntax "True" = "true"
toGallinaSyntax s = s

---------------------- string conversions
strToQId :: String -> G.Qualid
strToQId str = G.Bare (T.pack str)

strToGName :: String -> G.Name
strToGName str = G.Ident (strToQId str)

strToTerm :: String -> G.Term
strToTerm str = G.Qualid (strToQId str)

strToBinder :: String -> G.Binder
strToBinder s = G.Inferred G.Explicit (strToGName s)

---------------------- Name conversions (haskell AST)
nameToStr :: Show l => H.Name l -> String
nameToStr (H.Ident _ str) = str
nameToStr (H.Symbol _ str) = str

nameToText :: Show l => H.Name l -> T.Text
nameToText name = T.pack (toGallinaSyntax (nameToStr name))

nameToQId :: Show l => H.Name l -> G.Qualid
nameToQId name = G.Bare (nameToText name)

nameToGName :: Show l => H.Name l -> G.Name
nameToGName name = G.Ident (nameToQId name)

nameToTerm :: Show l => H.Name l -> G.Term
nameToTerm name = G.Qualid (nameToQId name)

nameToTypeTerm :: Show l => H.Name l -> G.Term
nameToTypeTerm name = getType (getString name)

patToQID :: Show l => H.Pat l -> G.Qualid
patToQID (H.PVar _ name) = nameToQId name

---------------------- QName conversion functions (Haskell AST)
qNameToStr :: Show l => H.QName l -> String
qNameToStr qName = T.unpack (qNameToText qName)

qNameToText :: Show l => H.QName l -> T.Text
qNameToText (H.UnQual _ name) = nameToText name
qNameToText (H.Special _ specCon) = specConToText specCon
qNameToText _ = error "qualified names not implemented"

qNameToQId :: Show l => H.QName l -> G.Qualid
qNameToQId qName = G.Bare (qNameToText qName)

qNameToGName :: Show l => H.QName l -> G.Name
qNameToGName (H.UnQual _ name) = nameToGName name
qNameToGName _ = error "qualified names not implemented"

qNameToTerm :: Show l => H.QName l -> G.Term
qNameToTerm qName = getConstr (getQString qName)

qNameToTypeTerm :: Show l => H.QName l -> G.Term
qNameToTypeTerm qName = getType (getQString qName)

qNameToBinder :: Show l => H.QName l -> G.Binder
qNameToBinder qName = G.Inferred G.Explicit (qNameToGName qName)

specConToText :: Show l => H.SpecialCon l -> T.Text
specConToText (H.Cons _) = T.pack "Cons"
specConToText (H.UnitCon _) = T.pack "unit"
specConToText con = error ("specialConstructor not implemented: " ++ show con)

---------------------- gName conversion functions (Coq AST)
gNameToStr :: G.Name -> String
gNameToStr (G.Ident qId) = qIdToStr qId

gNameToTerm :: G.Name -> G.Term
gNameToTerm (G.Ident qId) = G.Qualid qId

gNameToQId :: G.Name -> G.Qualid
gNameToQId (G.Ident qId) = qId

---------------------- argument conversion functions (Coq AST)
argToTerm :: G.Arg -> G.Term
argToTerm (G.PosArg term) = term

---------------------- binder conversion functions (Coq AST)
binderToArg :: G.Binder -> G.Arg
binderToArg (G.Typed _ _ (n B.:| _) _) = G.PosArg (gNameToTerm n)
binderToArg (G.Inferred _ n) = G.PosArg (gNameToTerm n)

---------------------- Qualid conversion functions (Coq AST)
qIdToStr :: G.Qualid -> String
qIdToStr (G.Bare ident) = T.unpack ident

qIdToGName :: G.Qualid -> G.Name
qIdToGName = G.Ident

addSuffixToQId :: G.Qualid -> G.Qualid
addSuffixToQId (G.Bare ident) = G.Bare (T.pack (T.unpack ident ++ "'"))

termToQId :: G.Term -> G.Qualid
termToQId (G.Qualid qId) = qId
termToQId (G.App constr _) = termToQId constr
termToQId term = error (show term)

---------------------- Conversion of Coq AST to strings
termToStrings :: G.Term -> [String]
termToStrings (G.Qualid qId) = [qIdToStr qId]
termToStrings (G.Parens term) = termToStrings term
termToStrings (G.App term args) = termToStrings term ++ listToStrings argToStrings (fromNonEmptyList args)
termToStrings (G.Match mItem _ equations) =
  listToStrings mItemToStrings (fromNonEmptyList mItem) ++ listToStrings equationToStrings equations
termToStrings (G.Arrow term1 term2) = termToStrings term1 ++ termToStrings term2

listToStrings :: (a -> [String]) -> [a] -> [String]
listToStrings = concatMap

argToStrings :: G.Arg -> [String]
argToStrings (G.PosArg term) = termToStrings term

mItemToStrings :: G.MatchItem -> [String]
mItemToStrings (G.MatchItem term _ _) = termToStrings term

equationToStrings :: G.Equation -> [String]
equationToStrings (G.Equation multPattern term) =
  listToStrings multPatToStrings (fromNonEmptyList multPattern) ++ termToStrings term

multPatToStrings :: G.MultPattern -> [String]
multPatToStrings (G.MultPattern (pat B.:| pats)) = listToStrings patToStrings patList
  where
    patList = pat : pats

patToStrings :: G.Pattern -> [String]
patToStrings (G.QualidPat qId) = [qIdToStr qId]
patToStrings (G.ArgsPat qId pats) = qIdToStr qId : patsToStrings pats
patToStrings G.UnderscorePat = ["_"]

patsToStrings :: [G.Pattern] -> [String]
patsToStrings = concatMap patToStrings

---------------------- Predefined Term
typeTerm :: G.Term
typeTerm = G.Sort G.Type

listTerm :: G.Term
listTerm = G.Qualid (strToQId "List")

pairTerm :: G.Term
pairTerm = G.Qualid (strToQId "Pair")

---------------------- Predefined Coq Types
coqTypes :: [G.Name]
coqTypes = [strToGName "nat", strToGName "bool", strToGName "option", strToGName "identity"]

haskellTypes :: [G.Qualid]
haskellTypes = [strToQId "Bool", strToQId "Option", strToQId "Identity", strToQId "Nat"]

--Convert qualifiedOperator from Haskell to Qualid with Operator signature
qOpToQOpId :: Show l => H.QOp l -> G.Qualid
qOpToQOpId (H.QVarOp _ qName) = G.Bare (T.pack ("op_" ++ qNameToStr qName ++ "__"))
qOpToQOpId (H.QConOp _ qName) = G.Bare (T.pack ("op_" ++ qNameToStr qName ++ "__"))

qOpToQId :: Show l => H.QOp l -> G.Qualid
qOpToQId (H.QVarOp _ qName) = qNameToQId qName
qOpToQId (H.QConOp _ qName) = qNameToQId qName
