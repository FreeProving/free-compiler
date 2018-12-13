module Coq.HelperFunctions where

import Language.Haskell.Exts.Syntax
import qualified Coq.Gallina as G

import qualified Data.Text as T

import qualified GHC.Base as B


--helper functions
unique :: Eq a => [a] -> [a]
unique []       =
  []
unique (x : xs) =
  x : unique (filter (x /=) xs)

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

getQString :: QName l -> String
getQString (UnQual _ name) =
  getString name

getString  :: Name l -> String
getString (Ident _ str) =
  str
getString (Symbol _ str) =
  str



toGallinaSyntax :: String -> String
toGallinaSyntax ("False") =
  "false"
toGallinaSyntax ("True") =
  "true"
toGallinaSyntax s =
  s

--manual covnversion of common Haskell types to coq equivalent
getType :: String -> G.Term
getType ("Int") =
  strToTerm "nat"
getType ("Bool") =
  strToTerm "bool"
getType str =
  strToTerm str

getTypeSignatureByName :: [G.TypeSignature] -> Name l -> Maybe G.TypeSignature
getTypeSignatureByName [] name =
  Nothing
getTypeSignatureByName (x : xs) name =
   if (nameEqTypeName x name)
    then Just x
    else getTypeSignatureByName xs name

isCoqType :: G.Name -> Bool
isCoqType name =
   null (filter (/= name) coqTypes)

isTypeSig :: Decl l -> Bool
isTypeSig (TypeSig _ _ _) =
 True
isTypeSig _ =
 False

filterEachElement :: [a] -> (a -> a -> Bool) -> [a] -> [a]
filterEachElement [] f _ =
  []
filterEachElement (x : xs) f list =
  filter (f x) list ++
  filterEachElement xs f list

-- name comparison functions
nameEqTypeName :: G.TypeSignature -> Name l -> Bool
nameEqTypeName (G.TypeSignature sigName _) name =
  gNameEqName sigName name

gNameEqName :: G.Name -> Name l -> Bool
gNameEqName (G.Ident (G.Bare gName)) (Ident _ name) =
  (T.unpack gName) == name

--string conversions
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

-----
getBinderName :: G.Binder -> G.Term
getBinderName (G.Inferred _ name) =
  gNameToTerm name
getBinderName (G.Typed _ _ (name B.:| xs) _) =
  gNameToTerm name

untypeBinder :: G.Binder -> G.Binder
untypeBinder (G.Typed _ _ (name B.:| xs) _) =
  G.Inferred G.Explicit name
untypeBinder binder =
  binder
---
addMonadicPrefix :: String -> G.Name -> G.Name
addMonadicPrefix str (G.Ident (G.Bare ident)) =
  G.Ident (strToQId (str ++ name))
  where
    name = T.unpack ident

addOptionPrefix :: G.Name -> G.Name
addOptionPrefix =
  addMonadicPrefix "o"

addMonadicPrefixToBinder :: (G.Name -> G.Name) -> G.Binder -> G.Binder
addMonadicPrefixToBinder f (G.Inferred expl name) =
  G.Inferred expl (f name)
addMonadicPrefixToBinder f (G.Typed gen expl (name B.:| xs) ty) =
  G.Typed gen expl (singleton (f name)) ty


toOptionTerm :: G.Term -> G.Term
toOptionTerm term =
  G.App optionTerm (singleton (G.PosArg term))

-- Predefined Terms
optionTerm :: G.Term
optionTerm =
  G.Qualid (strToQId "option")

returnTerm :: G.Term
returnTerm =
  G.Qualid (strToQId "return_")

bindOperator :: G.Term
bindOperator =
  G.Qualid (strToQId "op_>>=__")

typeTerm :: G.Term
typeTerm =
  G.Sort G.Type

toReturnTerm :: G.Term -> G.Term
toReturnTerm term =
  G.App returnTerm (singleton (G.PosArg (G.Parens term)))

coqTypes :: [G.Name]
coqTypes =
  strToGName "nat" :
  strToGName "bool" :
  strToGName "option" :
  []

-- Name conversions (haskell ast)
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

gNameToTerm :: G.Name -> G.Term
gNameToTerm (G.Ident (qId)) =
  G.Qualid qId

--QName conversion (Haskell ast)
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
  (nameToGName name)
qNameToGName _ =
  error "qualified names not implemented"

qNameToTerm :: QName l -> G.Term
qNameToTerm qName =
  G.Qualid (qNameToQId qName)

qNameToTypeTerm :: QName l -> G.Term
qNameToTypeTerm qName =
  getType (getQString qName)

argToTerm :: G.Arg -> G.Term
argToTerm (G.PosArg term) =
  term

getTypeFromBinder :: G.Binder -> G.Term
getTypeFromBinder (G.Typed _ _ _ term) =
  term

-- Qualid conversion functions
qIdToStr :: G.Qualid -> String
qIdToStr (G.Bare ident) =
  T.unpack ident

getNameFromQualConDecl :: QualConDecl l -> G.Qualid
getNameFromQualConDecl (QualConDecl _ _ _ (ConDecl _ name _)) =
  nameToQId name

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

hasNonInferrableConstr :: [QualConDecl l] -> Bool
hasNonInferrableConstr qConDecls =
  length (filter isNonInferrableConstr qConDecls) > 0

isNonInferrableConstr :: QualConDecl l -> Bool
isNonInferrableConstr (QualConDecl _ _ _ (ConDecl _ _ [])) =
  True
isNonInferrableConstr (QualConDecl _ _ _ (ConDecl _ _ ty)) =
  False

getNonInferrableConstrNames :: [QualConDecl l] -> [G.Qualid]
getNonInferrableConstrNames qConDecls =
  [ getNameFromQualConDecl d | d <- nonInferrableQConDecls]
  where
    nonInferrableQConDecls = filter isNonInferrableConstr qConDecls

-- Conversion of terms to strings
----------------------------------

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
listToStrings f list = concatMap f list


getTypeNamesFromTerm :: G.Term -> [G.Name]
getTypeNamesFromTerm (G.App term args) =
  map strToGName (termToStrings term) ++
    map strToGName (concat (map termToStrings (map argToTerm (nonEmptyListToList args))))
getTypeNamesFromTerm _ =
  []

getConstrNameFromType :: G.Term -> G.Name
getConstrNameFromType (G.App term _) =
  head (map strToGName (termToStrings term))
getConstrNameFromType _ =
  strToGName ""

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
multPatToStrings (G.MultPattern pattern) =
  listToStrings patToStrings (nonEmptyListToList pattern)

patToStrings :: G.Pattern -> [String]
patToStrings (G.QualidPat qId) =
  [qIdToStr qId]
patToStrings (G.ArgsPat qId pats) =
  qIdToStr qId : patsToStrings pats
patToStrings (G.UnderscorePat) =
  ["_"]

patsToStrings :: [G.Pattern] -> [String]
patsToStrings [] =
  []
patsToStrings (p : ps) =
  patToStrings p ++
    patsToStrings ps


--Convert qualifiedOperator from Haskell to Qualid with Operator signature
qOpToQId :: QOp l -> G.Qualid
qOpToQId (QVarOp _ qName) =
  G.Bare (T.pack ("op_"++ (qNameToStr qName) ++"__"))
qOpToQId (QConOp _ qName) =
  error "not implemented"
