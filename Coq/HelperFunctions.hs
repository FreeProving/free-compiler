module Coq.HelperFunctions where

import Language.Haskell.Exts.Syntax
import qualified Coq.Gallina as G

import qualified Data.Text as T

import qualified GHC.Base as B


--helper functions
unique :: Eq a => [a] -> [a]
unique []       = []
unique (x : xs) = x : unique (filter (x /=) xs)

--convert single element to nonempty list
singleton :: a -> B.NonEmpty a
singleton a = a B.:| []

toNonemptyList :: [a] -> B.NonEmpty a
toNonemptyList (x:xs) = x B.:| xs

nonEmptyListToList :: B.NonEmpty a -> [a]
nonEmptyListToList (x B.:| xs) = x : xs

getQString :: QName l -> String
getQString (UnQual _ name) = getString name

getString  :: Name l -> String
getString (Ident _ str) = str
getString (Symbol _ str) = str

toGallinaSyntax :: String -> String
toGallinaSyntax ("False") = "false"
toGallinaSyntax ("True") = "true"
toGallinaSyntax ("Maybe") = "option"
toGallinaSyntax ("Nothing") = "None"
toGallinaSyntax ("Just") = "Some"
toGallinaSyntax s = s

--manual covnversion of common Haskell types to coq equivalent
getType :: String -> G.Term
getType ("Int") = strToTerm "nat"
getType ("Bool") = strToTerm "bool"
getType str = strToTerm str

getTypeSignatureByName :: [G.TypeSignature] -> Name l -> Maybe G.TypeSignature
getTypeSignatureByName [] name = Nothing
getTypeSignatureByName (x : xs) name = if (nameEqTypeName x name)
                                      then Just x
                                      else getTypeSignatureByName xs name

isCoqType :: G.Name -> Bool
isCoqType name =
   null (filter (/= name) coqTypes)

filterEachElement :: [a] -> (a -> a -> Bool) -> [a] -> [a]
filterEachElement [] f _ = []
filterEachElement (x : xs) f list = filter (f x) list ++ filterEachElement xs f list

-- name comparison functions
nameEqTypeName :: G.TypeSignature -> Name l -> Bool
nameEqTypeName (G.TypeSignature sigName _) name = gNameEqName sigName name

gNameEqName :: G.Name -> Name l -> Bool
gNameEqName (G.Ident (G.Bare gName)) (Ident _ name) = (T.unpack gName) == name

--string conversions
strToQId :: String -> G.Qualid
strToQId str = G.Bare (T.pack str)

strToGName :: String -> G.Name
strToGName str = G.Ident (strToQId str)

strToTerm :: String -> G.Term
strToTerm str = G.Qualid (strToQId str)

strToBinder :: String -> G.Binder
strToBinder s =
  G.Inferred G.Explicit (strToGName s)

termToOptionTerm :: G.Term -> G.Term
termToOptionTerm term =
  G.App optionTerm (singleton (G.PosArg term))

optionTerm :: G.Term
optionTerm =
  G.Qualid (strToQId "option")

coqTypes :: [G.Name]
coqTypes = strToGName "nat" : strToGName "bool" : strToGName "option" : []

-- Name conversions (haskell ast)
nameToStr :: Name l -> String
nameToStr (Ident _ str) = str
nameToStr (Symbol _ str) = str

nameToText :: Name l -> T.Text
nameToText name = T.pack (toGallinaSyntax (nameToStr name))

nameToQId :: Name l -> G.Qualid
nameToQId name = G.Bare (nameToText name)

nameToGName :: Name l -> G.Name
nameToGName name = G.Ident (nameToQId name)

nameToTerm :: Name l -> G.Term
nameToTerm name = G.Qualid (nameToQId name)

nameToTypeTerm :: Name l -> G.Term
nameToTypeTerm name = getType (getString name)

--QName conversion (Haskell ast)
qNameToStr :: QName l -> String
qNameToStr qName = T.unpack (qNameToText qName)

qNameToText :: QName l -> T.Text
qNameToText (UnQual _ name) = nameToText name
qNameToText _ = error "not implemented"

qNameToQId :: QName l -> G.Qualid
qNameToQId qName = G.Bare (qNameToText qName)

qNameToGName :: QName l -> G.Name
qNameToGName (UnQual _ name) = (nameToGName name)
qNameToGName _ = error "not implemented"

qNameToTerm :: QName l -> G.Term
qNameToTerm qName = G.Qualid (qNameToQId qName)

qNameToTypeTerm :: QName l -> G.Term
qNameToTypeTerm qName = getType (getQString qName)

argToTerm :: G.Arg -> G.Term
argToTerm (G.PosArg term) = term


-- Qualid conversion functions
qIdToStr :: G.Qualid -> String
qIdToStr (G.Bare ident) = T.unpack ident

getNameFromQualConDecl :: QualConDecl l -> G.Qualid
getNameFromQualConDecl (QualConDecl _ _ _ (ConDecl _ name _)) = nameToQId name


--Convert qualifiedOperator from Haskell to Qualid with Operator signature
qOpToQId :: QOp l -> G.Qualid
qOpToQId (QVarOp _ qName) = G.Bare (T.pack ("op_"++ (qNameToStr qName) ++"__"))
qOpToQId (QConOp _ qName) = error "not implemented"
