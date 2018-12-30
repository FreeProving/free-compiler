module Compiler.HelperFunctions where

import Language.Haskell.Exts.Syntax
import qualified Language.Coq.Gallina as G

import qualified Data.Text as T

import qualified GHC.Base as B

data ConversionMode =
  HelperFunction
  | FueledFunction
  deriving(Eq, Show, Read)

data ConversionMonad =
  Option
  | Identity
  deriving(Eq, Show, Read)

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

getStringFromGName :: G.Name -> String
getStringFromGName (G.Ident qId) =
  getStringFromQId qId
getStringFromGName G.UnderscoreName =
  "_"

getStringFromQId :: G.Qualid -> String
getStringFromQId (G.Bare text) = T.unpack text


toGallinaSyntax :: String -> String
toGallinaSyntax "False" =
  "false"
toGallinaSyntax "True" =
  "true"
toGallinaSyntax s =
  s

--manual covnversion of common Haskell types to coq equivalent
getType :: String -> G.Term
getType "Int" =
  strToTerm "nat"
getType "Bool" =
  strToTerm "bool"
getType str =
  strToTerm str

getTypeSignatureByName :: [G.TypeSignature] -> Name l -> Maybe G.TypeSignature
getTypeSignatureByName [] name =
  Nothing
getTypeSignatureByName (x : xs) name =
   if nameEqTypeName x name
    then Just x
    else getTypeSignatureByName xs name

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

getReturnType :: G.TypeSignature -> G.Term
getReturnType (G.TypeSignature _ terms) = last terms

filterEachElement :: [a] -> (a -> a -> Bool) -> [a] -> [a]
filterEachElement [] f list =
  list
filterEachElement (x : xs) f list =
    filterEachElement xs f filteredList
  where
    filteredList  = filter (f x) list

-- name comparison functions
nameEqTypeName :: G.TypeSignature -> Name l -> Bool
nameEqTypeName (G.TypeSignature sigName _ ) =
  gNameEqName sigName

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

removeMonadFromBinder :: G.Binder -> G.Binder
removeMonadFromBinder (G.Typed gen expl (n B.:| xs) term) =
  G.Typed gen expl (singleton (removeMonadicPrefix n)) (fromMonadicTerm term)

transformBindersMonadic :: [G.Binder] -> ConversionMonad -> [G.Binder]
transformBindersMonadic binders m =
  [transformBinderMonadic b m | b <- binders]

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

--return Binder that fits a certain Type Signature
findFittingBinder :: [G.Binder] -> G.Term -> G.Binder
findFittingBinder binders ty =
  head (filter (\x -> ty == getBinderType x) binders)

addDecrFuelArgument :: B.NonEmpty G.Arg -> B.NonEmpty G.Arg
addDecrFuelArgument list =
  toNonemptyList (nonEmptyListToList list ++ [G.PosArg decrFuelTerm] )

convertArgumentsToTerms :: [G.Arg] -> [G.Term]
convertArgumentsToTerms args =
  [(\(G.PosArg x) -> x) a |a <- args ]

convertTermsToArguments :: [G.Term] -> [G.Arg]
convertTermsToArguments terms =
  [G.PosArg t | t <- terms]

binderToArg :: G.Binder -> G.Arg
binderToArg (G.Typed _ _ (n B.:| _) _ ) =
  G.PosArg (gNameToTerm n)
binderToArg (G.Inferred _ n) =
  G.PosArg (gNameToTerm n)

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

isAppTerm :: G.Term -> Bool
isAppTerm (G.App _ _ ) = True
isAppTerm _ = False
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

getBinderType :: G.Binder -> G.Term
getBinderType (G.Typed _ _ _ term) =
  term
---
addMonadicPrefix :: String -> G.Name -> G.Name
addMonadicPrefix str (G.Ident (G.Bare ident)) =
  G.Ident (strToQId (str ++ name))
  where
    name = T.unpack ident

removeMonadicPrefix :: G.Name -> G.Name
removeMonadicPrefix name =
  strToGName (tail (getStringFromGName name))

addOptionPrefix :: G.Name -> G.Name
addOptionPrefix =
  addMonadicPrefix "o"

addIdentityPrefix :: G.Name -> G.Name
addIdentityPrefix =
  addMonadicPrefix "i"

addMonadicPrefixToBinder ::  ConversionMonad -> G.Binder -> G.Binder
addMonadicPrefixToBinder m (G.Inferred expl name) =
  G.Inferred expl (getPrefixFromMonad m name)
addMonadicPrefixToBinder m (G.Typed gen expl (name B.:| xs) ty) =
  G.Typed gen expl (singleton (getPrefixFromMonad m name)) ty

getPrefixFromMonad :: ConversionMonad -> (G.Name -> G.Name)
getPrefixFromMonad Option = addOptionPrefix
getPrefixFromMonad Identity = addIdentityPrefix

addFuelBinder :: [G.Binder] -> [G.Binder]
addFuelBinder binders = binders ++ [fuelBinder]

toOptionTerm :: G.Term -> G.Term
toOptionTerm term =
  G.App optionTerm (singleton (G.PosArg term))

toIdentityTerm :: G.Term -> G.Term
toIdentityTerm term =
  G.App identityTerm (singleton (G.PosArg term))

fromMonadicTerm :: G.Term -> G.Term
fromMonadicTerm (G.App _ (G.PosArg term B.:| xs)) =
  term
fromMonadicTerm term =
  term
-- Predefined Terms
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

decrFuelTerm :: G.Term
decrFuelTerm =
  G.Qualid (strToQId "rFuel")

fuelBinder :: G.Binder
fuelBinder =
  G.Typed G.Ungeneralizable G.Explicit fuelName natTerm
  where
    natTerm = G.Qualid (strToQId "nat")
    fuelName = singleton (strToGName "fuel")

typeTerm :: G.Term
typeTerm =
  G.Sort G.Type

toReturnTerm :: G.Term -> G.Term
toReturnTerm term =
  G.App returnTerm (singleton (G.PosArg (G.Parens term)))

coqTypes :: [G.Name]
coqTypes =
  [strToGName "nat",
  strToGName "bool",
  strToGName "option"]


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
gNameToTerm (G.Ident qId) =
  G.Qualid qId

gNameToQId :: G.Name -> G.Qualid
gNameToQId (G.Ident qId) = qId

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
  nameToGName name
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
hasNonInferrableConstr =
  any isNonInferrableConstr

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
listToStrings  = concatMap


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


--Convert qualifiedOperator from Haskell to Qualid with Operator signature
qOpToQId :: QOp l -> G.Qualid
qOpToQId (QVarOp _ qName) =
  G.Bare (T.pack ("op_"++ qNameToStr qName ++"__"))
qOpToQId (QConOp _ qName) =
  error "qualified Constr Operators not implemented"
