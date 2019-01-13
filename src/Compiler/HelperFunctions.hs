module Compiler.HelperFunctions where

import Language.Haskell.Exts.Syntax
import qualified Language.Coq.Gallina as G


import qualified Data.Text as T

import qualified GHC.Base as B
import Data.Maybe (isJust)
import Data.List (nub)


---------------------- NonemptyList Conversions
--convert single element to nonempty list
singleton :: a -> B.NonEmpty a
singleton a =
  a B.:| []

toNonemptyList :: [a] -> B.NonEmpty a
toNonemptyList (x:xs) =
  x B.:| xs

nonEmptyListToList :: B.NonEmpty a -> [a]
nonEmptyListToList (x B.:| xs) =
  x : xs

---------------------- Getter Functions
--Get Strings From Data Structures
getQString :: QName l -> String
getQString (UnQual _ name) =
  getString name

getString  :: Name l -> String
getString (Ident _ str) =
  str
getString (Symbol _ str) =
  str

getStringFromGName :: G.Name -> String
getStringFromGName (G.Ident qId) =
  getStringFromQId qId
getStringFromGName G.UnderscoreName =
  "_"

getStringFromQId :: G.Qualid -> String
getStringFromQId (G.Bare text) = T.unpack text

--manual covnversion of common Haskell types to coq equivalent
getType :: String -> G.Term
getType "Int" =
  strToTerm "nat"
getType "Bool" =
  strToTerm "bool"
getType "String" =
  strToTerm "string"
getType str =
  strToTerm str

getTypeSignatureByName :: [G.TypeSignature] -> Name l -> Maybe G.TypeSignature
getTypeSignatureByName [] name =
  Nothing
getTypeSignatureByName (x : xs) name =
   if typeNameEqName x name
    then Just x
    else getTypeSignatureByName xs name

getTypeSignatureByQId :: [G.TypeSignature] -> G.Qualid -> Maybe G.TypeSignature
getTypeSignatureByQId [] _ =
  Nothing
getTypeSignatureByQId (x : xs) qId =
  if typeNameEqQId x qId
    then Just x
    else getTypeSignatureByQId xs qId

getNamesFromDataDecls :: [Decl l] -> [G.Name]
getNamesFromDataDecls sentences =
  [getNameFromDataDecl s | s <- sentences]

getNameFromDataDecl :: Decl l -> G.Name
getNameFromDataDecl (DataDecl _ _ _ declHead _ _ ) =
  getNameFromDeclHead declHead

getNameFromDeclHead :: DeclHead l -> G.Name
getNameFromDeclHead (DHead _ name) =
  nameToGName name
getNameFromDeclHead (DHParen _ declHead) =
  getNameFromDeclHead declHead
getNameFromDeclHead (DHApp _ declHead _) =
  getNameFromDeclHead declHead

getReturnTypeFromDeclHead :: [G.Arg] -> DeclHead l -> G.Term
getReturnTypeFromDeclHead [] dHead =
  applyToDeclHead dHead nameToTerm
getReturnTypeFromDeclHead (x : xs) dHead =
  G.App (applyToDeclHead dHead nameToTerm) (x B.:| xs)

getNonInferrableConstrNames :: [QualConDecl l] -> [G.Qualid]
getNonInferrableConstrNames qConDecls =
  [ getNameFromQualConDecl d | d <- nonInferrableQConDecls]
  where
    nonInferrableQConDecls = filter isNonInferrableConstr qConDecls

getNameFromQualConDecl :: QualConDecl l -> G.Qualid
getNameFromQualConDecl (QualConDecl _ _ _ (ConDecl _ name _)) =
  nameToQId name

getTypeNamesFromTerm :: G.Term -> [G.Name]
getTypeNamesFromTerm (G.App term args) =
  map strToGName (termToStrings term) ++
    map strToGName (concatMap (termToStrings . argToTerm) (nonEmptyListToList args))
getTypeNamesFromTerm _ =
  []

getConstrNameFromType :: G.Term -> G.Name
getConstrNameFromType (G.App term _) =
  head (map strToGName (termToStrings term))
getConstrNameFromType _ =
  strToGName ""

getReturnType :: G.TypeSignature -> G.Term
getReturnType (G.TypeSignature _ terms) = last terms

getBinderName :: G.Binder -> G.Term
getBinderName (G.Inferred _ name) =
  gNameToTerm name
getBinderName (G.Typed _ _ (name B.:| xs) _) =
  gNameToTerm name

getBinderType :: G.Binder -> G.Term
getBinderType (G.Typed _ _ _ term) =
  term

getBinderByQId :: [G.Binder] -> G.Qualid -> Maybe G.Binder
getBinderByQId [] _ =
  Nothing
getBinderByQId (x : xs) qId =
  if eqQId qId (termToQId (getBinderName x))
    then Just x
    else getBinderByQId xs qId

getPatternFromMultPattern :: G.MultPattern -> [G.Pattern]
getPatternFromMultPattern (G.MultPattern pats) =
  nonEmptyListToList pats

getQIdsFromPattern :: G.Pattern -> [G.Qualid]
getQIdsFromPattern (G.ArgsPat _ pats) =
  concatMap getQIdsFromPattern pats
getQIdsFromPattern (G.QualidPat qId) =
  [qId]
getQIdsFromPattern pat =
  []

---------------------- Bool Functions
isCoqType :: G.Name -> Bool
isCoqType name =
   not (any (eqGName name) coqTypes)

isTypeSig :: Decl l -> Bool
isTypeSig TypeSig {} =
 True
isTypeSig _ =
 False

isDataDecl :: Decl l -> Bool
isDataDecl DataDecl {} =
  True
isDataDecl _ =
  False

hasNonInferrableConstr :: [QualConDecl l] -> Bool
hasNonInferrableConstr =
  any isNonInferrableConstr

isNonInferrableConstr :: QualConDecl l -> Bool
isNonInferrableConstr (QualConDecl _ _ _ (ConDecl _ _ [])) =
  True
isNonInferrableConstr (QualConDecl _ _ _ (ConDecl _ _ ty)) =
  False

containsRecursiveCall :: G.Term -> G.Qualid -> Bool
containsRecursiveCall (G.App term args) funName =
  containsRecursiveCall term funName || or [containsRecursiveCall t funName | t <- argTerms]
  where
    argTerms = convertArgumentsToTerms (nonEmptyListToList args)
containsRecursiveCall (G.Parens term) funName =
  containsRecursiveCall term funName
containsRecursiveCall (G.Qualid qId) funName =
  eqQId qId funName
containsRecursiveCall _ _ = False

isRecursiveFunction :: G.Term -> [G.TypeSignature] -> Bool
isRecursiveFunction (G.Qualid qId) typeSigs =
  isJust (getTypeSignatureByQId typeSigs qId)


isAppTerm :: G.Term -> Bool
isAppTerm (G.App _ _ ) = True
isAppTerm _ = False

isQualidTerm :: G.Term -> Bool
isQualidTerm (G.Qualid _ ) = True
isQualidTerm _ = False

-- name comparison functions
gNameEqName :: G.Name -> Name l -> Bool
gNameEqName (G.Ident (G.Bare gName)) (Ident _ name) =
  T.unpack gName == name

eqGName :: G.Name -> G.Name -> Bool
eqGName gNameL gNameR =
  getStringFromGName gNameL == getStringFromGName gNameR

eqQId :: G.Qualid -> G.Qualid -> Bool
eqQId qIdL qIdR =
   getStringFromQId qIdL == getStringFromQId qIdR

qIdEqBinder :: G.Qualid -> G.Binder -> Bool
qIdEqBinder qId (G.Typed _ _ (n B.:| _ ) _ ) =
  eqQId qId (gNameToQId n)
qIdEqBinder qId (G.Inferred _ n) =
  eqQId qId (gNameToQId n)

dataTypeUneqGName :: G.Name -> G.Name -> Bool
dataTypeUneqGName dataType gName =
  nameString /= dataString
  where
    dataString = getStringFromGName dataType
    nameString = getStringFromGName gName

typeNameEqName :: G.TypeSignature -> Name l -> Bool
typeNameEqName (G.TypeSignature sigName _ ) =
  gNameEqName sigName

typeNameEqQId :: G.TypeSignature -> G.Qualid -> Bool
typeNameEqQId (G.TypeSignature sigName _ ) =
  eqQId (gNameToQId sigName)

---------------------- various helper functions

filterEachElement :: [a] -> (a -> a -> Bool) -> [a] -> [a]
filterEachElement [] f list =
  list
filterEachElement (x : xs) f list =
    filterEachElement xs f filteredList
  where
    filteredList  = filter (f x) list

--return Binder that fits a certain Type Signature
findFittingBinder :: [G.Binder] -> G.Term -> G.Binder
findFittingBinder binders ty =
  head (filter (\x -> ty == getBinderType x) binders)

addInferredTypesToSignature :: [G.Binder] -> [G.Name] -> [G.Binder]
addInferredTypesToSignature binders dataNames =
  if null filteredTypeNames
    then binders
    else G.Typed G.Ungeneralizable G.Explicit (toNonemptyList filteredTypeNames) typeTerm : binders
  where
    filteredTypeNames = nub (filterEachElement dataNames dataTypeUneqGName (filter isCoqType typeNames))
    typeNames = concatMap getTypeNamesFromTerm typeTerms
    typeTerms = map getBinderType binders
    consNames = nub (map getConstrNameFromType typeTerms)

convertArgumentsToTerms :: [G.Arg] -> [G.Term]
convertArgumentsToTerms args =
  map argToTerm args

convertTermsToArguments :: [G.Term] -> [G.Arg]
convertTermsToArguments terms =
  map G.PosArg terms

collapseApp :: G.Term -> G.Term
collapseApp (G.App term args) =
  if isAppTerm term
    then G.App funName (toNonemptyList combinedArgs)
    else G.App term args
    where
      funName = returnAppName term
      combinedArgs = combineArgs (nonEmptyListToList args) term
collapseApp (G.Parens term) =
  G.Parens (collapseApp term)
collapseApp term = term

returnAppName :: G.Term -> G.Term
returnAppName (G.App term _) =
  returnAppName term
returnAppName term = term

combineArgs :: [G.Arg] -> G.Term -> [G.Arg]
combineArgs args (G.App term args' ) =
  combineArgs combArgs term
  where
    combArgs = nonEmptyListToList args' ++ args
combineArgs args _ =
  convertTermsToArguments (map collapseApp (convertArgumentsToTerms args))

--apply a function only to the actual head of a DeclHead
applyToDeclHead :: DeclHead l -> (Name l -> a) -> a
applyToDeclHead (DHead _ name) f =
  f name
applyToDeclHead (DHApp _ declHead _ ) f =
  applyToDeclHead declHead f

--apply a function to every tyVarBind of a DeclHead and reverse it (to get arguments in right order)
applyToDeclHeadTyVarBinds :: DeclHead l -> (TyVarBind l -> a ) -> [a]
applyToDeclHeadTyVarBinds (DHead _ _) f =
  []
applyToDeclHeadTyVarBinds (DHApp _ declHead tyVarBind) f =
  reverse (f tyVarBind : reverse (applyToDeclHeadTyVarBinds declHead f))


toGallinaSyntax :: String -> String
toGallinaSyntax "False" =
  "false"
toGallinaSyntax "True" =
  "true"
toGallinaSyntax s =
  s

---------------------- string conversions
strToQId :: String -> G.Qualid
strToQId str =
  G.Bare (T.pack str)

strToGName :: String -> G.Name
strToGName str =
  G.Ident (strToQId str)

strToTerm :: String -> G.Term
strToTerm str =
  G.Qualid (strToQId str)

strToBinder :: String -> G.Binder
strToBinder s =
  G.Inferred G.Explicit (strToGName s)

---------------------- Name conversions (haskell AST)
nameToStr :: Name l -> String
nameToStr (Ident _ str) =
  str
nameToStr (Symbol _ str) =
  str

nameToText :: Name l -> T.Text
nameToText name =
  T.pack (toGallinaSyntax (nameToStr name))

nameToQId :: Name l -> G.Qualid
nameToQId name =
  G.Bare (nameToText name)

nameToGName :: Name l -> G.Name
nameToGName name =
  G.Ident (nameToQId name)

nameToTerm :: Name l -> G.Term
nameToTerm name =
  G.Qualid (nameToQId name)

nameToTypeTerm :: Name l -> G.Term
nameToTypeTerm name =
  getType (getString name)

---------------------- QName conversion functions (Haskell AST)
qNameToStr :: QName l -> String
qNameToStr qName =
  T.unpack (qNameToText qName)

qNameToText :: QName l -> T.Text
qNameToText (UnQual _ name) =
  nameToText name
qNameToText _ =
  error "qualified names not implemented"

qNameToQId :: QName l -> G.Qualid
qNameToQId qName =
  G.Bare (qNameToText qName)

qNameToGName :: QName l -> G.Name
qNameToGName (UnQual _ name) =
  nameToGName name
qNameToGName _ =
  error "qualified names not implemented"

qNameToTerm :: QName l -> G.Term
qNameToTerm qName =
  G.Qualid (qNameToQId qName)

qNameToTypeTerm :: QName l -> G.Term
qNameToTypeTerm qName =
  getType (getQString qName)

qNameToBinder :: Show l => QName l -> G.Binder
qNameToBinder qName =
  G.Inferred G.Explicit (qNameToGName qName)



---------------------- gName conversion functions (Coq AST)
gNameToTerm :: G.Name -> G.Term
gNameToTerm (G.Ident qId) =
  G.Qualid qId

gNameToQId :: G.Name -> G.Qualid
gNameToQId (G.Ident qId) = qId

---------------------- argument conversion functions (Coq AST)
argToTerm :: G.Arg -> G.Term
argToTerm (G.PosArg term) =
  term

---------------------- binder conversion functions (Coq AST)
binderToArg :: G.Binder -> G.Arg
binderToArg (G.Typed _ _ (n B.:| _) _ ) =
  G.PosArg (gNameToTerm n)
binderToArg (G.Inferred _ n) =
  G.PosArg (gNameToTerm n)

---------------------- Qualid conversion functions (Coq AST)
qIdToStr :: G.Qualid -> String
qIdToStr (G.Bare ident) =
  T.unpack ident

qIdToGName :: G.Qualid -> G.Name
qIdToGName = G.Ident

termToQId :: G.Term -> G.Qualid
termToQId (G.Qualid qId) = qId

---------------------- Conversion of Coq AST to strings

termToStrings :: G.Term -> [String]
termToStrings (G.Qualid qId) =
  [qIdToStr qId]
termToStrings (G.Parens term) =
  termToStrings term
termToStrings (G.App term args) =
  termToStrings term ++
    listToStrings argToStrings (nonEmptyListToList args)
termToStrings (G.Match mItem _ equations) =
  listToStrings mItemToStrings (nonEmptyListToList mItem)  ++
    listToStrings equationToStrings equations

listToStrings :: (a -> [String]) -> [a] -> [String]
listToStrings  = concatMap

argToStrings :: G.Arg -> [String]
argToStrings (G.PosArg term) =
  termToStrings term

mItemToStrings :: G.MatchItem -> [String]
mItemToStrings (G.MatchItem term _ _) =
  termToStrings term

equationToStrings :: G.Equation -> [String]
equationToStrings (G.Equation multPattern term) =
  listToStrings multPatToStrings (nonEmptyListToList multPattern)  ++
    termToStrings term

multPatToStrings :: G.MultPattern -> [String]
multPatToStrings (G.MultPattern (pat B.:| pats)) =
  listToStrings patToStrings patList
  where
    patList = pat : pats

patToStrings :: G.Pattern -> [String]
patToStrings (G.QualidPat qId) =
  [qIdToStr qId]
patToStrings (G.ArgsPat qId pats) =
  qIdToStr qId : patsToStrings pats
patToStrings G.UnderscorePat =
  ["_"]

patsToStrings :: [G.Pattern] -> [String]
patsToStrings = concatMap patToStrings


---------------------- Predefined Term
typeTerm :: G.Term
typeTerm =
  G.Sort G.Type

---------------------- Predefined Coq Types
coqTypes :: [G.Name]
coqTypes =
  [strToGName "nat",
  strToGName "bool",
  strToGName "option"]

--Convert qualifiedOperator from Haskell to Qualid with Operator signature
qOpToQId :: QOp l -> G.Qualid
qOpToQId (QVarOp _ qName) =
  G.Bare (T.pack ("op_"++ qNameToStr qName ++"__"))
qOpToQId (QConOp _ qName) =
  error "qualified Constr Operators not implemented"
