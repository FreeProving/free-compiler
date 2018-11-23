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

isTypeSignature :: Decl l -> Bool
isTypeSignature (TypeSig _ _ _) = True
isTypeSignature _ = False

isNoTypeSignature :: Decl l -> Bool
isNoTypeSignature decl = not (isTypeSignature decl)

filterForTypeSignatures :: Decl l -> G.TypeSignature
filterForTypeSignatures (TypeSig _ (name : rest) types) = G.TypeSignature (nameToGName name) (convertTypes types)

convertTypes :: Type l -> [G.Term]
convertTypes (TyFun _ type1 type2) = mappend (convertTypes type1) (convertTypes type2)
convertTypes (TyCon _ qName) = [qNameToTypeTerm qName]

convertModuleDecl :: Decl l -> [G.TypeSignature] -> G.Sentence
convertModuleDecl (FunBind _ (x : xs)) typeSigs = G.DefinitionSentence (convertMatchDef x typeSigs)
convertModuleDecl _ _ = error "not Inmplemented"

convertMatchDef :: Match l -> [G.TypeSignature] -> G.Definition
convertMatchDef (Match _ name pattern rhs _) typeSigs =
  let
    typeSig :: Maybe G.TypeSignature
    typeSig = (getTypeSignatureByName typeSigs name)
  in
    G.DefinitionDef G.Global (nameToQId name) (convertPatsToBinders pattern typeSig) (convertReturnType typeSig) (convertRhsToTerm rhs)

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

--manual covnversion of common Haskell types to coq equivalent
getType :: String -> G.Term
getType ("Int") = strToTerm "nat"
getType ("Bool") = strToTerm "bool"

--helper functions
--convert single element to nonempty list
toNonemptyList :: a -> B.NonEmpty a
toNonemptyList a = a B.:| []

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

-- name comparrison functions
nameEqTypeName :: G.TypeSignature -> Name l -> Bool
nameEqTypeName (G.TypeSignature sigName _) name = gNameEqName sigName name

gNameEqName :: G.Name -> Name l -> Bool
gNameEqName (G.Ident (G.Bare gName)) (Ident _ name) = (T.unpack gName) == name


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
nameToText :: Name l -> T.Text
nameToText (Ident _ str) = strToText str
nameToText (Symbol _ str) = strToText str

nameToQId :: Name l -> G.Qualid
nameToQId name = G.Bare (nameToText name)

nameToGName :: Name l -> G.Name
nameToGName name = G.Ident (nameToQId name)

nameToTerm :: Name l -> G.Term
nameToTerm name = G.Qualid (nameToQId name)

--QName conversion (Haskell ast)
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

--Convert qualifiedOperator from Haskell to Qualid with Operator signature
qOpToQId :: QOp l -> G.Qualid
qOpToQId (QVarOp _ (UnQual _ (Symbol _ name))) = G.Bare (T.pack ("op_"++ name ++"__"))
qOpToQId _ = error "not implemented"

--print the converted module
printCoqAST :: G.LocalModule -> IO ()
printCoqAST x = putDoc (renderGallina x)
