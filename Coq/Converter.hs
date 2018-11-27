module Coq.Converter where

import Language.Haskell.Exts.Syntax
import qualified Coq.Gallina as G
import Coq.Pretty
import Text.PrettyPrint.Leijen.Text

import qualified GHC.Base as B

import qualified Data.Text as T

convertModule :: Module l -> G.LocalModule
convertModule (Module _ (Just modHead) _ _ decls) = G.LocalModule (convertModuleHead modHead) (convertModuleDecls (filter isNoTypeSignature decls) (map filterForTypeSignatures (filter isTypeSignature decls)))
convertModule (Module _ Nothing _ _ decls)        = error "not implemented"

convertModuleHead :: ModuleHead l -> G.Ident
convertModuleHead (ModuleHead _ (ModuleName _ modName) _ _) = T.pack modName

convertModuleDecls :: [Decl l] -> [G.TypeSignature]-> [G.Sentence]
convertModuleDecls decls typeSigs = [convertModuleDecl s typeSigs | s <- decls]

convertModuleDecl :: Decl l -> [G.TypeSignature] -> G.Sentence
convertModuleDecl (FunBind _ (x : xs)) typeSigs = convertMatchDef x typeSigs
convertModuleDecl (DataDecl _ (DataType _ ) Nothing declHead qConDecl _ ) _ = G.InductiveSentence (convertDataTypeDecl declHead qConDecl)
convertModuleDecl _ _ = error "not Inmplemented"



convertDataTypeDecl :: DeclHead l -> [QualConDecl l] -> G.Inductive
convertDataTypeDecl dHead qConDecl = G.Inductive (toNonemptyList(G.IndBody (applyToDeclHead dHead nameToQId) (applyToDeclHeadTyVarBinds dHead convertTyVarBindToBinder) typeTerm (convertQConDeclsToGConDecls qConDecl (getReturnTypeFromDeclHead (applyToDeclHeadTyVarBinds dHead convertTyVarBindToArg) dHead)))) []

convertMatchDef :: Match l -> [G.TypeSignature] -> G.Sentence
convertMatchDef (Match _ name pattern rhs _) typeSigs =
      let
        typeSig = (getTypeSignatureByName typeSigs name)
      in
        if(isRecursive name rhs)
          then
            G.FixpointSentence (convertMatchToFixpoint name pattern rhs typeSig)
          else
            G.DefinitionSentence (convertMatchToDefinition name pattern rhs typeSig)

convertMatchToDefinition :: Name l -> [Pat l] -> Rhs l -> Maybe G.TypeSignature -> G.Definition
convertMatchToDefinition name pattern rhs typeSig  = G.DefinitionDef G.Global (nameToQId name) (convertPatsToBinders pattern typeSig) (convertReturnType typeSig) (convertRhsToTerm rhs)

convertMatchToFixpoint :: Name l -> [Pat l] -> Rhs l -> Maybe G.TypeSignature -> G.Fixpoint
convertMatchToFixpoint name pattern rhs  typeSig = G.Fixpoint (toNonemptyList (G.FixBody (nameToQId name) (listToNonemptyList (convertPatsToBinders pattern typeSig)) Nothing Nothing (convertRhsToTerm  rhs))) []

getReturnTypeFromDeclHead :: [G.Arg] -> DeclHead l -> G.Term
getReturnTypeFromDeclHead [] dHead = applyToDeclHead dHead nameToTerm
getReturnTypeFromDeclHead (x : xs) dHead = G.App (applyToDeclHead dHead nameToTerm) (x B.:| xs)

convertTyVarBindToBinder :: TyVarBind l -> G.Binder
convertTyVarBindToBinder (KindedVar _ name kind) = error "not implemented"
convertTyVarBindToBinder (UnkindedVar _ name) = G.Typed G.Ungeneralizable G.Explicit (toNonemptyList (nameToGName name)) typeTerm

convertTyVarBindToArg :: TyVarBind l -> G.Arg
convertTyVarBindToArg (KindedVar _ name kind) = error "not implemented"
convertTyVarBindToArg (UnkindedVar _ name) = G.PosArg (nameToTerm name)

convertQConDeclsToGConDecls :: [QualConDecl l] -> G.Term -> [(G.Qualid, [G.Binder], Maybe G.Term)]
convertQConDeclsToGConDecls qConDecl term = [convertQConDeclToGConDecl c term | c <- qConDecl]

convertQConDeclToGConDecl :: QualConDecl l -> G.Term -> (G.Qualid, [G.Binder], Maybe G.Term)
convertQConDeclToGConDecl (QualConDecl _ Nothing Nothing (ConDecl _ name types)) term = ((nameToQId name), [] , (Just (convertToArrowTerm types term)))

convertToArrowTerm :: [Type l] -> G.Term -> G.Term
convertToArrowTerm [] returnType = returnType
convertToArrowTerm (x : xs) returnType = G.Arrow (convertTypeToTerm x) (convertToArrowTerm xs returnType)

filterForTypeSignatures :: Decl l -> G.TypeSignature
filterForTypeSignatures (TypeSig _ (name : rest) types) = G.TypeSignature (nameToGName name) (convertTypeToTerms types)

convertTypeToTerm :: Type l -> G.Term
convertTypeToTerm (TyVar _ name) = nameToTerm name
convertTypeToTerm (TyCon _ qName) = qNameToTerm qName
convertTypeToTerm (TyParen _ ty) = G.Parens (convertTypeToTerm ty)
convertTypeToTerm (TyApp _ type1 type2) = G.App (convertTypeToTerm type1) (toNonemptyList (convertTypeToArg type2))
convertTypeToTerm _ = error "not implemented"

convertTypeToArg :: Type l -> G.Arg
convertTypeToArg ty = G.PosArg (convertTypeToTerm ty)

convertTypeToTerms :: Type l -> [G.Term]
convertTypeToTerms (TyFun _ type1 type2) = mappend (convertTypeToTerms type1) (convertTypeToTerms type2)
convertTypeToTerms t = [convertTypeToTerm t]

convertReturnType :: Maybe G.TypeSignature -> Maybe G.Term
convertReturnType Nothing = Nothing
convertReturnType (Just (G.TypeSignature _ types)) = Just (last types)

convertPatsToBinders :: [Pat l] -> Maybe G.TypeSignature-> [G.Binder]
convertPatsToBinders patList Nothing = [convertPatToBinder p | p <- patList]
convertPatsToBinders patList (Just (G.TypeSignature _ typeList)) = convertPatsAndTypeSigsToBinders patList (init typeList)

convertPatToBinder :: Pat l -> G.Binder
convertPatToBinder (PVar _ name) = G.Inferred G.Explicit (nameToGName name)
convertPatToBinder _ = error "not implemented"

convertPatsAndTypeSigsToBinders :: [Pat l] -> [G.Term] -> [G.Binder]
convertPatsAndTypeSigsToBinders [] [] = []
convertPatsAndTypeSigsToBinders p [] = []
convertPatsAndTypeSigsToBinders [] t = []
convertPatsAndTypeSigsToBinders (p : ps) (t : ts) = (convertPatAndTypeSigToBinder p t) : convertPatsAndTypeSigsToBinders ps ts

convertPatAndTypeSigToBinder :: Pat l -> G.Term -> G.Binder
convertPatAndTypeSigToBinder (PVar _ name) term = G.Typed G.Ungeneralizable G.Explicit (toNonemptyList (nameToGName name)) term
convertPatAndTypeSigToBinder _ _ = error "not implemented"

convertRhsToTerm :: Rhs l -> G.Term
convertRhsToTerm (UnGuardedRhs _ expr) = convertExprToTerm expr
convertRhsToTerm (GuardedRhss _ _ ) = error "not implemented"

convertExprToTerm :: Exp l -> G.Term
convertExprToTerm (Var _ qName) = qNameToTerm qName
convertExprToTerm (Con _ qName) = qNameToTerm qName
convertExprToTerm (Paren _ expr) = G.Parens (convertExprToTerm expr)
convertExprToTerm (App _ expr1 expr2) = G.App (convertExprToTerm expr1) (toNonemptyList (G.PosArg (convertExprToTerm expr2)))
convertExprToTerm (InfixApp _ (Var _ qNameL) (qOp) (Var _ qNameR)) = (G.App (G.Qualid (qOpToQId qOp)) ((G.PosArg (G.Qualid (qNameToQId qNameL))) B.:| (G.PosArg (G.Qualid (qNameToQId qNameR))) : []))
convertExprToTerm (Case _ expr altList) = G.Match (toNonemptyList (G.MatchItem (convertExprToTerm expr)  Nothing Nothing)) Nothing (convertAltListToEquationList altList)
convertExprToTerm _ = error "not implemented"

convertAltListToEquationList :: [Alt l] -> [G.Equation]
convertAltListToEquationList altList = [convertAltToEquation s | s <- altList]

convertAltToEquation :: Alt l -> G.Equation
convertAltToEquation (Alt _ pat rhs _) = G.Equation (toNonemptyList (G.MultPattern (toNonemptyList(convertHPatToGPat pat)))) (convertRhsToTerm rhs)

convertHPatListToGPatList :: [Pat l] -> [G.Pattern]
convertHPatListToGPatList patList = [convertHPatToGPat s | s <- patList]

convertHPatToGPat :: Pat l -> G.Pattern
convertHPatToGPat (PVar _ name) = G.QualidPat (nameToQId name)
convertHPatToGPat (PApp _ qName pList) = G.ArgsPat (qNameToQId qName) (convertHPatListToGPatList pList)
convertHPatToGPat _ = error "not implemented"

convertQNameToBinder :: QName l -> G.Binder
convertQNameToBinder qName = G.Inferred G.Explicit (qNameToGName qName)

isTypeSignature :: Decl l -> Bool
isTypeSignature (TypeSig _ _ _) = True
isTypeSignature _ = False

isNoTypeSignature :: Decl l -> Bool
isNoTypeSignature decl = not (isTypeSignature decl)

typeTerm :: G.Term
typeTerm = strToTerm "Type"

--manual covnversion of common Haskell types to coq equivalent
getType :: String -> G.Term
getType ("Int") = strToTerm "nat"
getType ("Bool") = strToTerm "bool"

--apply a function only to the actual head of a DeclHead
applyToDeclHead :: DeclHead l -> (Name l -> a) -> a
applyToDeclHead (DHead _ name) f = f name
applyToDeclHead (DHApp _ declHead _ ) f = applyToDeclHead declHead f

--apply a function to every tyVarBind of a DeclHead and reverse it (to get arguments in right order)
applyToDeclHeadTyVarBinds :: DeclHead l -> (TyVarBind l -> a ) -> [a]
applyToDeclHeadTyVarBinds (DHead _ _) f = []
applyToDeclHeadTyVarBinds (DHApp _ declHead tyVarBind) f = reverse (f tyVarBind : applyToDeclHeadTyVarBinds declHead f)

--helper functions
--convert single element to nonempty list
toNonemptyList :: a -> B.NonEmpty a
toNonemptyList a = a B.:| []

listToNonemptyList :: [a] -> B.NonEmpty a
listToNonemptyList (x:xs) = x B.:| xs

nonEmptyListToList :: B.NonEmpty a -> [a]
nonEmptyListToList (x B.:| xs) = x : xs

getQString :: QName l -> String
getQString (UnQual _ name) = getString name

getString  :: Name l -> String
getString (Ident _ str) = str
getString (Symbol _ str) = str

getTypeSignatureByName :: [G.TypeSignature] -> Name l -> Maybe G.TypeSignature
getTypeSignatureByName [] name = Nothing
getTypeSignatureByName (x : xs) name = if (nameEqTypeName x name)
                                      then Just x
                                      else getTypeSignatureByName xs name

-- name comparison functions
nameEqTypeName :: G.TypeSignature -> Name l -> Bool
nameEqTypeName (G.TypeSignature sigName _) name = gNameEqName sigName name

gNameEqName :: G.Name -> Name l -> Bool
gNameEqName (G.Ident (G.Bare gName)) (Ident _ name) = (T.unpack gName) == name

--check if function is recursive
isRecursive :: Name l -> Rhs l -> Bool
isRecursive name rhs = length (filter (== (getString name)) (termToStrings (convertRhsToTerm rhs))) > 0

termToStrings :: G.Term -> [String]
termToStrings (G.Qualid qId) = [qIdToStr qId]
termToStrings (G.Parens term) = termToStrings term
termToStrings (G.App term args) = mappend (termToStrings term) (listToStrings (nonEmptyListToList args) argToStrings)
termToStrings (G.Match mItem _ equations) = mappend (listToStrings (nonEmptyListToList mItem) mItemToStrings) (listToStrings equations equationToStrings)
termToStrings _ = error "not implemented"

listToStrings :: [a] -> (a -> [String]) -> [String]
listToStrings [] f = []
listToStrings (x : xs) f = mappend (f x) (listToStrings xs f)

argToStrings :: G.Arg -> [String]
argToStrings (G.PosArg term) = termToStrings term

mItemToStrings :: G.MatchItem -> [String]
mItemToStrings (G.MatchItem term _ _) = termToStrings term

equationToStrings :: G.Equation -> [String]
equationToStrings (G.Equation multPattern term) = mappend (listToStrings (nonEmptyListToList multPattern) multPatToStrings) (termToStrings term)

multPatToStrings :: G.MultPattern -> [String]
multPatToStrings (G.MultPattern pattern) = listToStrings (nonEmptyListToList pattern) patToStrings

patToStrings :: G.Pattern -> [String]
patToStrings (G.QualidPat qId) = [qIdToStr qId]
patToStrings (G.ArgsPat qId pats) = qIdToStr qId : patsToStrings pats

patsToStrings :: [G.Pattern] -> [String]
patsToStrings [] = []
patsToStrings (p : ps) = mappend (patToStrings p) (patsToStrings ps)

textToStr :: T.Text -> String
textToStr text = T.unpack text

--string conversions
strToText :: String -> T.Text
strToText str = T.pack str

strToQId :: String -> G.Qualid
strToQId str = G.Bare (strToText str)

strToGName :: String -> G.Name
strToGName str = G.Ident (strToQId str)

strToTerm :: String -> G.Term
strToTerm str = G.Qualid (strToQId str)

-- Name conversions (haskell ast)
nameToStr :: Name l -> String
nameToStr (Ident _ str) = str
nameToStr (Symbol _ str) = str

nameToText :: Name l -> T.Text
nameToText name = strToText (nameToStr name)

nameToQId :: Name l -> G.Qualid
nameToQId name = G.Bare (nameToText name)

nameToGName :: Name l -> G.Name
nameToGName name = G.Ident (nameToQId name)

nameToTerm :: Name l -> G.Term
nameToTerm name = G.Qualid (nameToQId name)

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

-- Qualid conversion functions
qIdToStr :: G.Qualid -> String
qIdToStr (G.Bare ident) = textToStr ident


--Convert qualifiedOperator from Haskell to Qualid with Operator signature
qOpToQId :: QOp l -> G.Qualid
qOpToQId (QVarOp _ qName) = G.Bare (T.pack ("op_"++ (qNameToStr qName) ++"__"))
qOpToQId (QConOp _ qName) = error "not implemented"

--print the converted module
printCoqAST :: G.LocalModule -> IO ()
printCoqAST x = putDoc (renderGallina x)
