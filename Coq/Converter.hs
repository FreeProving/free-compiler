module Coq.Converter where

import Language.Haskell.Exts.Syntax
import qualified Coq.Gallina as G
import Coq.HelperFunctions
import Coq.Pretty
import Text.PrettyPrint.Leijen.Text

import qualified GHC.Base as B

import qualified Data.Text as T
import Data.List (partition)


convertModule :: Module l -> G.LocalModule
convertModule (Module _ (Just modHead) _ _ decls) = G.LocalModule (convertModuleHead modHead)
                                                      (convertModuleDecls otherDecls $ map filterForTypeSignatures typeSigs)
                                                    where
                                                      (typeSigs, otherDecls) = partition isTypeSig decls
convertModule (Module _ Nothing _ _ decls)        = G.LocalModule (T.pack "unnamed")
                                                      (convertModuleDecls otherDecls $ map filterForTypeSignatures typeSigs)
                                                    where
                                                      (typeSigs, otherDecls) = partition isTypeSig decls

convertModuleHead :: ModuleHead l -> G.Ident
convertModuleHead (ModuleHead _ (ModuleName _ modName) _ _) = T.pack modName

convertModuleDecls :: [Decl l] -> [G.TypeSignature]-> [G.Sentence]
convertModuleDecls ((FunBind _ (x : xs)) : ds) typeSigs = convertMatchDef x typeSigs : convertModuleDecls ds typeSigs
convertModuleDecls ((DataDecl _ (DataType _ ) Nothing declHead qConDecl _ ) : ds) typeSigs =
    if needsArgumentsSentence declHead qConDecl
      then [G.InductiveSentence  (convertDataTypeDecl declHead qConDecl)] ++
                                convertArgumentSentences declHead qConDecl ++
                                convertModuleDecls ds typeSigs
      else G.InductiveSentence  (convertDataTypeDecl declHead qConDecl) :
                                convertModuleDecls ds typeSigs
convertModuleDecls [] _ = []
convertModuleDecls _ _ = error "Top-level declaration not implemented"


needsArgumentsSentence :: DeclHead l -> [QualConDecl l] -> Bool
needsArgumentsSentence declHead qConDecls = length binders > 0 && hasNonInferrableConstr qConDecls
                                          where
                                            binders = applyToDeclHeadTyVarBinds declHead convertTyVarBindToBinder

hasNonInferrableConstr :: [QualConDecl l] -> Bool
hasNonInferrableConstr qConDecls = length (filter isNonInferrableConstr qConDecls) > 0

isNonInferrableConstr :: QualConDecl l -> Bool
isNonInferrableConstr (QualConDecl _ _ _ (ConDecl _ _ [])) = True
isNonInferrableConstr (QualConDecl _ _ _ (ConDecl _ _ ty)) = False

convertArgumentSentences :: DeclHead l -> [QualConDecl l] -> [G.Sentence]
convertArgumentSentences declHead qConDecls = [G.ArgumentsSentence (G.Arguments Nothing con (convertArgumentSpec declHead)) | con <- constrToDefine]
                                              where
                                                constrToDefine = getNonInferrableConstrNames qConDecls

getNonInferrableConstrNames :: [QualConDecl l] -> [G.Qualid]
getNonInferrableConstrNames qConDecls = [ getNameFromQualConDecl d | d <- nonInferrableQConDecls]
                                        where
                                          nonInferrableQConDecls = filter isNonInferrableConstr qConDecls
convertArgumentSpec :: DeclHead l -> [G.ArgumentSpec]
convertArgumentSpec declHead = [G.ArgumentSpec G.ArgImplicit varName Nothing | varName <- varNames]
                               where
                                 varNames = applyToDeclHeadTyVarBinds declHead convertTyVarBindToName
convertDataTypeDecl :: DeclHead l -> [QualConDecl l] -> G.Inductive
convertDataTypeDecl dHead qConDecl = G.Inductive (singleton $ G.IndBody typeName binders typeTerm constrDecls) []
                                    where
                                      typeName = applyToDeclHead dHead nameToQId
                                      binders = applyToDeclHeadTyVarBinds dHead convertTyVarBindToBinder
                                      constrDecls = convertQConDecls
                                                      qConDecl
                                                        (getReturnTypeFromDeclHead (applyToDeclHeadTyVarBinds dHead convertTyVarBindToArg) dHead)

convertMatchDef :: Match l -> [G.TypeSignature] -> G.Sentence
convertMatchDef (Match _ name pattern rhs _) typeSigs =
    if isRecursive name rhs
      then G.FixpointSentence (convertMatchToFixpoint name pattern rhs typeSig)
      else G.DefinitionSentence (convertMatchToDefinition name pattern rhs typeSig)
    where
      typeSig = getTypeSignatureByName typeSigs name

convertMatchToDefinition :: Name l -> [Pat l] -> Rhs l -> Maybe G.TypeSignature -> G.Definition
convertMatchToDefinition name pattern rhs typeSig  = G.DefinitionDef G.Global (nameToQId name)
                                                                                (convertPatsToBinders pattern typeSig)
                                                                                  (convertReturnType typeSig)
                                                                                    (convertRhsToTerm rhs)

convertMatchToFixpoint :: Name l -> [Pat l] -> Rhs l -> Maybe G.TypeSignature -> G.Fixpoint
convertMatchToFixpoint name pattern rhs  typeSig = G.Fixpoint (singleton (G.FixBody (nameToQId name)
                                                                                      (toNonemptyList (convertPatsToBinders pattern typeSig))
                                                                                        Nothing
                                                                                          Nothing
                                                                                            (convertRhsToTerm  rhs))) []

getReturnTypeFromDeclHead :: [G.Arg] -> DeclHead l -> G.Term
getReturnTypeFromDeclHead [] dHead = applyToDeclHead dHead nameToTerm
getReturnTypeFromDeclHead (x : xs) dHead = G.App (applyToDeclHead dHead nameToTerm) (x B.:| xs)

convertTyVarBindToName :: TyVarBind l -> G.Name
convertTyVarBindToName (KindedVar _ name _) = nameToGName name
convertTyVarBindToName (UnkindedVar _ name) = nameToGName name

convertTyVarBindToBinder :: TyVarBind l -> G.Binder
convertTyVarBindToBinder (KindedVar _ name kind) = error "Kind-annotation not implemented"
convertTyVarBindToBinder (UnkindedVar _ name) = G.Typed G.Ungeneralizable G.Explicit (singleton (nameToGName name)) typeTerm

convertTyVarBindToArg :: TyVarBind l -> G.Arg
convertTyVarBindToArg (KindedVar _ name kind) = error "Kind-annotation not implemented"
convertTyVarBindToArg (UnkindedVar _ name) = G.PosArg (nameToTerm name)

convertQConDecls :: [QualConDecl l] -> G.Term -> [(G.Qualid, [G.Binder], Maybe G.Term)]
convertQConDecls qConDecl term = [convertQConDecl c term | c <- qConDecl]

convertQConDecl :: QualConDecl l -> G.Term -> (G.Qualid, [G.Binder], Maybe G.Term)
convertQConDecl (QualConDecl _ Nothing Nothing (ConDecl _ name types)) term = ((nameToQId name), [] , (Just (convertToArrowTerm types term)))

convertToArrowTerm :: [Type l] -> G.Term -> G.Term
convertToArrowTerm types returnType = buildArrowTerm (map convertTypeToTerm types) returnType

buildArrowTerm :: [G.Term] -> G.Term -> G.Term
buildArrowTerm terms returnType = foldr G.Arrow returnType terms

filterForTypeSignatures :: Decl l -> G.TypeSignature
filterForTypeSignatures (TypeSig _ (name : rest) types) = G.TypeSignature (nameToGName name)
                                                                            (convertTypeToTerms types)

convertTypeToArg :: Type l -> G.Arg
convertTypeToArg ty = G.PosArg (convertTypeToTerm ty)

convertTypeToTerm :: Type l -> G.Term
convertTypeToTerm (TyVar _ name) = nameToTypeTerm name
convertTypeToTerm (TyCon _ qName) = qNameToTypeTerm qName
convertTypeToTerm (TyParen _ ty) = G.Parens (convertTypeToTerm ty)
convertTypeToTerm (TyApp _ type1 type2) = G.App (convertTypeToTerm type1) (singleton (convertTypeToArg type2))
convertTypeToTerm _ = error "Haskell-type not implemented"

convertTypeToTerms :: Type l -> [G.Term]
convertTypeToTerms (TyFun _ type1 type2) = convertTypeToTerms type1 ++ convertTypeToTerms type2
convertTypeToTerms t = [convertTypeToTerm t]

convertReturnType :: Maybe G.TypeSignature -> Maybe G.Term
convertReturnType Nothing = Nothing
convertReturnType (Just (G.TypeSignature _ types)) = Just (last types)

convertPatsToBinders :: [Pat l] -> Maybe G.TypeSignature-> [G.Binder]
convertPatsToBinders patList Nothing = [convertPatToBinder p | p <- patList]
convertPatsToBinders patList (Just (G.TypeSignature _ typeList)) = convertPatsAndTypeSigsToBinders patList (init typeList)

convertPatToBinder :: Pat l -> G.Binder
convertPatToBinder (PVar _ name) = G.Inferred G.Explicit (nameToGName name)
convertPatToBinder _ = error "Pattern not implemented"

convertPatsAndTypeSigsToBinders :: [Pat l] -> [G.Term] -> [G.Binder]
convertPatsAndTypeSigsToBinders pats typeSigs = zipWith convertPatAndTypeSigToBinder pats typeSigs

convertPatAndTypeSigToBinder :: Pat l -> G.Term -> G.Binder
convertPatAndTypeSigToBinder (PVar _ name) term = G.Typed G.Ungeneralizable G.Explicit (singleton (nameToGName name)) term
convertPatAndTypeSigToBinder _ _ = error "Haskell pattern not implemented"

convertRhsToTerm :: Rhs l -> G.Term
convertRhsToTerm (UnGuardedRhs _ expr) = convertExprToTerm expr
convertRhsToTerm (GuardedRhss _ _ ) = error "Guards not implemented"

convertExprToTerm :: Exp l -> G.Term
convertExprToTerm (Var _ qName) = qNameToTerm qName
convertExprToTerm (Con _ qName) = qNameToTerm qName
convertExprToTerm (Paren _ expr) = G.Parens (convertExprToTerm expr)
convertExprToTerm (App _ expr1 expr2) = G.App (convertExprToTerm expr1) (singleton (G.PosArg (convertExprToTerm expr2)))
convertExprToTerm (InfixApp _ (Var _ qNameL) (qOp) (Var _ qNameR)) = (G.App (G.Qualid (qOpToQId qOp))
                                                                              ((G.PosArg (G.Qualid (qNameToQId qNameL))) B.:| (G.PosArg (G.Qualid (qNameToQId qNameR))) : []))
convertExprToTerm (Case _ expr altList) = G.Match (singleton (G.MatchItem (convertExprToTerm expr)  Nothing Nothing))
                                                    Nothing
                                                      (convertAltListToEquationList altList)
convertExprToTerm _ = error "Haskell expression not implemented"

convertAltListToEquationList :: [Alt l] -> [G.Equation]
convertAltListToEquationList altList = [convertAltToEquation s | s <- altList]

convertAltToEquation :: Alt l -> G.Equation
convertAltToEquation (Alt _ pat rhs _) = G.Equation (singleton (G.MultPattern (singleton(convertHPatToGPat pat)))) (convertRhsToTerm rhs)

convertHPatListToGPatList :: [Pat l] -> [G.Pattern]
convertHPatListToGPatList patList = [convertHPatToGPat s | s <- patList]

convertHPatToGPat :: Pat l -> G.Pattern
convertHPatToGPat (PVar _ name) = G.QualidPat (nameToQId name)
convertHPatToGPat (PApp _ qName pList) = G.ArgsPat (qNameToQId qName) (convertHPatListToGPatList pList)
convertHPatToGPat _ = error "Haskell pattern not implemented"

convertQNameToBinder :: QName l -> G.Binder
convertQNameToBinder qName = G.Inferred G.Explicit (qNameToGName qName)

isTypeSig :: Decl l -> Bool
isTypeSig (TypeSig _ _ _) = True
isTypeSig _ = False

typeTerm :: G.Term
typeTerm = G.Sort G.Type

--apply a function only to the actual head of a DeclHead
applyToDeclHead :: DeclHead l -> (Name l -> a) -> a
applyToDeclHead (DHead _ name) f = f name
applyToDeclHead (DHApp _ declHead _ ) f = applyToDeclHead declHead f

--apply a function to every tyVarBind of a DeclHead and reverse it (to get arguments in right order)
applyToDeclHeadTyVarBinds :: DeclHead l -> (TyVarBind l -> a ) -> [a]
applyToDeclHeadTyVarBinds (DHead _ _) f = []
applyToDeclHeadTyVarBinds (DHApp _ declHead tyVarBind) f = reverse (f tyVarBind : applyToDeclHeadTyVarBinds declHead f)



--check if function is recursive
isRecursive :: Name l -> Rhs l -> Bool
isRecursive name rhs = length (filter (== (getString name)) (termToStrings (convertRhsToTerm rhs))) > 0

termToStrings :: G.Term -> [String]
termToStrings (G.Qualid qId) = [qIdToStr qId]
termToStrings (G.Parens term) = termToStrings term
termToStrings (G.App term args) = termToStrings term ++ listToStrings (nonEmptyListToList args) argToStrings
termToStrings (G.Match mItem _ equations) = listToStrings (nonEmptyListToList mItem) mItemToStrings ++
                                              listToStrings equations equationToStrings

listToStrings :: [a] -> (a -> [String]) -> [String]
listToStrings [] f = []
listToStrings (x : xs) f = f x ++ listToStrings xs f

argToStrings :: G.Arg -> [String]
argToStrings (G.PosArg term) = termToStrings term

mItemToStrings :: G.MatchItem -> [String]
mItemToStrings (G.MatchItem term _ _) = termToStrings term

equationToStrings :: G.Equation -> [String]
equationToStrings (G.Equation multPattern term) = listToStrings (nonEmptyListToList multPattern) multPatToStrings ++ termToStrings term

multPatToStrings :: G.MultPattern -> [String]
multPatToStrings (G.MultPattern pattern) = listToStrings (nonEmptyListToList pattern) patToStrings

patToStrings :: G.Pattern -> [String]
patToStrings (G.QualidPat qId) = [qIdToStr qId]
patToStrings (G.ArgsPat qId pats) = qIdToStr qId : patsToStrings pats

patsToStrings :: [G.Pattern] -> [String]
patsToStrings [] = []
patsToStrings (p : ps) = patToStrings p ++ patsToStrings ps


--print the converted module
printCoqAST :: G.LocalModule -> IO ()
printCoqAST x = putDoc (renderGallina x)
