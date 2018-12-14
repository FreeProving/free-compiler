module Coq.Converter where

import Language.Haskell.Exts.Syntax
import qualified Coq.Gallina as G
import Coq.HelperFunctions
import Coq.Pretty
import Coq.Monad
import Text.PrettyPrint.Leijen.Text

import qualified GHC.Base as B

import qualified Data.Text as T
import Data.List (partition)



convertModule :: Module l -> G.LocalModule
convertModule (Module _ (Just modHead) _ _ decls) =
  G.LocalModule (convertModuleHead modHead)
    (monadDefinitions ++
      dataSentences ++
        (convertModuleDecls rDecls (map filterForTypeSignatures typeSigs) dataNames))
  where
    (typeSigs, otherDecls) = partition isTypeSig decls
    (dataDecls, rDecls) = partition isDataDecl otherDecls
    dataSentences = convertModuleDecls dataDecls (map filterForTypeSignatures typeSigs) []
    dataNames = getNamesFromDataDecls dataDecls
convertModule (Module _ Nothing _ _ decls) =
  G.LocalModule (T.pack "unnamed")
    (convertModuleDecls otherDecls  (map filterForTypeSignatures typeSigs) [])
  where
    (typeSigs, otherDecls) = partition isTypeSig decls

convertModuleHead :: ModuleHead l -> G.Ident
convertModuleHead (ModuleHead _ (ModuleName _ modName) _ _) =
  T.pack modName

--
convertModuleDecls :: [Decl l] -> [G.TypeSignature] -> [G.Name] -> [G.Sentence]
convertModuleDecls ((FunBind _ (x : xs)) : ds) typeSigs dataNames =
  convertMatchDef x typeSigs dataNames : convertModuleDecls ds typeSigs dataNames
convertModuleDecls ((DataDecl _ (DataType _ ) Nothing declHead qConDecl _ ) : ds) typeSigs dataNames =
    if needsArgumentsSentence declHead qConDecl
      then [G.InductiveSentence  (convertDataTypeDecl declHead qConDecl)] ++
                                convertArgumentSentences declHead qConDecl ++
                                convertModuleDecls ds typeSigs dataNames
      else G.InductiveSentence  (convertDataTypeDecl declHead qConDecl) :
                                convertModuleDecls ds typeSigs dataNames
convertModuleDecls [] _ _ =
  []
convertModuleDecls _ _ _ =
   error "Top-level declaration not implemented"


convertArgumentSentences :: DeclHead l -> [QualConDecl l] -> [G.Sentence]
convertArgumentSentences declHead qConDecls =
  [G.ArgumentsSentence (G.Arguments Nothing con (convertArgumentSpec declHead)) | con <- constrToDefine]
  where
    constrToDefine = getNonInferrableConstrNames qConDecls

convertArgumentSpec :: DeclHead l -> [G.ArgumentSpec]
convertArgumentSpec declHead =
  [G.ArgumentSpec G.ArgMaximal varName Nothing | varName <- varNames]
  where
   varNames = applyToDeclHeadTyVarBinds declHead convertTyVarBindToName

convertDataTypeDecl :: DeclHead l -> [QualConDecl l] -> G.Inductive
convertDataTypeDecl dHead qConDecl =
  G.Inductive (singleton $ G.IndBody typeName binders typeTerm constrDecls) []
    where
      typeName = applyToDeclHead dHead nameToQId
      binders = applyToDeclHeadTyVarBinds dHead convertTyVarBindToBinder
      constrDecls = convertQConDecls
                      qConDecl
                        (getReturnTypeFromDeclHead (applyToDeclHeadTyVarBinds dHead convertTyVarBindToArg) dHead)

convertMatchDef :: Match l -> [G.TypeSignature] -> [G.Name] -> G.Sentence
convertMatchDef (Match _ name pattern rhs _) typeSigs dataNames =
    if isRecursive name rhs
      then G.FixpointSentence (convertMatchToFixpoint name pattern rhs typeSig dataNames)
      else G.DefinitionSentence (convertMatchToDefinition name pattern rhs typeSig)
    where
      typeSig = getTypeSignatureByName typeSigs name

convertMatchToDefinition :: Name l -> [Pat l] -> Rhs l -> Maybe G.TypeSignature -> G.Definition
convertMatchToDefinition name pattern rhs typeSig  =
  G.DefinitionDef G.Global (nameToQId name)
    monadicBinders
      (convertReturnType typeSig)
        rhsTerm
  where
    monadicBinders = transformBindersMonadic (map (addMonadicPrefixToBinder addOptionPrefix) binders) toOptionTerm
    binders = convertPatsToBinders pattern typeSig
    rhsTerm = addBindOperators binders (convertRhsToTerm rhs)

convertMatchToFixpoint :: Name l -> [Pat l] -> Rhs l -> Maybe G.TypeSignature -> [G.Name] -> G.Fixpoint
convertMatchToFixpoint name pattern rhs typeSig dataNames =
  G.Fixpoint (singleton $ G.FixBody (nameToQId name)
    (toNonemptyList (bindersWithInferredTypes))
      Nothing
        Nothing
          rhsTerm) []
  where
    binders = convertPatsToBinders pattern typeSig
    bindersWithFuel = addFuelBinder (transformBindersMonadic (map (addMonadicPrefixToBinder addOptionPrefix) binders) toOptionTerm)
    bindersWithInferredTypes = addInferredTypesToSignature bindersWithFuel dataNames
    rhsTerm = addBindOperators binders (convertRhsToTerm rhs)

getReturnTypeFromDeclHead :: [G.Arg] -> DeclHead l -> G.Term
getReturnTypeFromDeclHead [] dHead =
  applyToDeclHead dHead nameToTerm
getReturnTypeFromDeclHead (x : xs) dHead =
  G.App (applyToDeclHead dHead nameToTerm) (x B.:| xs)

convertTyVarBindToName :: TyVarBind l -> G.Name
convertTyVarBindToName (KindedVar _ name _) =
  nameToGName name
convertTyVarBindToName (UnkindedVar _ name) =
  nameToGName name

convertTyVarBindToBinder :: TyVarBind l -> G.Binder
convertTyVarBindToBinder (KindedVar _ name kind) =
  error "Kind-annotation not implemented"
convertTyVarBindToBinder (UnkindedVar _ name) =
  G.Typed G.Ungeneralizable G.Explicit (singleton $ nameToGName name) typeTerm

convertTyVarBindToArg :: TyVarBind l -> G.Arg
convertTyVarBindToArg (KindedVar _ name kind) =
  error "Kind-annotation not implemented"
convertTyVarBindToArg (UnkindedVar _ name) =
  G.PosArg (nameToTerm name)

convertQConDecls :: [QualConDecl l] -> G.Term -> [(G.Qualid, [G.Binder], Maybe G.Term)]
convertQConDecls qConDecl term =
  [convertQConDecl c term | c <- qConDecl]

convertQConDecl :: QualConDecl l -> G.Term -> (G.Qualid, [G.Binder], Maybe G.Term)
convertQConDecl (QualConDecl _ Nothing Nothing (ConDecl _ name types)) term =
  ((nameToQId name), [] , (Just (convertToArrowTerm types term)))

convertToArrowTerm :: [Type l] -> G.Term -> G.Term
convertToArrowTerm types returnType =
  buildArrowTerm (map convertTypeToMonadicTerm types) returnType

buildArrowTerm :: [G.Term] -> G.Term -> G.Term
buildArrowTerm terms returnType =
  foldr G.Arrow returnType terms

filterForTypeSignatures :: Decl l -> G.TypeSignature
filterForTypeSignatures (TypeSig _ (name : rest) types) =
  G.TypeSignature (nameToGName name)
    (convertTypeToTerms types)

convertTypeToArg :: Type l -> G.Arg
convertTypeToArg ty =
  G.PosArg (convertTypeToTerm ty)

convertTypeToMonadicTerm :: Type l -> G.Term
convertTypeToMonadicTerm (TyVar _ name) =
  toOptionTerm $ nameToTypeTerm name
convertTypeToMonadicTerm (TyCon _ qName) =
  toOptionTerm $ qNameToTypeTerm qName
convertTypeToMonadicTerm (TyParen _ ty) =
  toOptionTerm $ G.Parens $ convertTypeToTerm ty
convertTypeToMonadicTerm ty =
  convertTypeToTerm ty

convertTypeToTerm :: Type l -> G.Term
convertTypeToTerm (TyVar _ name) =
  nameToTypeTerm name
convertTypeToTerm (TyCon _ qName) =
  qNameToTypeTerm qName
convertTypeToTerm (TyParen _ ty) =
  G.Parens (convertTypeToTerm ty)
convertTypeToTerm (TyApp _ type1 type2) =
  G.App (convertTypeToTerm type1) (singleton $ convertTypeToArg type2)
convertTypeToTerm _ =
  error "Haskell-type not implemented"

convertTypeToTerms :: Type l -> [G.Term]
convertTypeToTerms (TyFun _ type1 type2) =
  convertTypeToTerms type1 ++
    convertTypeToTerms type2
convertTypeToTerms t =
  [convertTypeToTerm t]

convertReturnType :: Maybe G.TypeSignature -> Maybe G.Term
convertReturnType Nothing =
  Nothing
convertReturnType (Just (G.TypeSignature _ types)) =
  Just (toOptionTerm (last types))

convertPatsToBinders :: [Pat l] -> Maybe G.TypeSignature -> [G.Binder]
convertPatsToBinders patList Nothing =
  [convertPatToBinder p | p <- patList]
convertPatsToBinders patList (Just (G.TypeSignature _ typeList)) =
  convertPatsAndTypeSigsToBinders patList (init typeList)

convertPatToBinder :: Pat l -> G.Binder
convertPatToBinder (PVar _ name) =
  G.Inferred G.Explicit (nameToGName name)
convertPatToBinder _ =
  error "Pattern not implemented"

convertPatsAndTypeSigsToBinders :: [Pat l] -> [G.Term] -> [G.Binder]
convertPatsAndTypeSigsToBinders pats typeSigs =
  zipWith convertPatAndTypeSigToBinder pats typeSigs

convertPatAndTypeSigToBinder :: Pat l -> G.Term -> G.Binder
convertPatAndTypeSigToBinder (PVar _ name) term =
  G.Typed G.Ungeneralizable G.Explicit (singleton $ nameToGName name) term
convertPatAndTypeSigToBinder _ _ =
  error "Haskell pattern not implemented"

addInferredTypesToSignature :: [G.Binder] -> [G.Name] -> [G.Binder]
addInferredTypesToSignature binders dataNames =
  if null filteredTypeNames
    then binders
    else (G.Typed G.Ungeneralizable G.Explicit (toNonemptyList (filteredTypeNames)) typeTerm) : binders
  where
    filteredTypeNames = unique $ filterEachElement dataNames dataTypeUneqGName (filter isCoqType typeNames)
    typeNames = concat (map getTypeNamesFromTerm typeTerms)
    typeTerms = map getTypeFromBinder binders
    consNames = unique (map getConstrNameFromType typeTerms)

convertRhsToTerm :: Rhs l -> G.Term
convertRhsToTerm (UnGuardedRhs _ expr) =
  convertExprToTerm expr
convertRhsToTerm (GuardedRhss _ _ ) =
  error "Guards not implemented"


addBindOperators :: [G.Binder] -> G.Term -> G.Term
addBindOperators [] term =
  toReturnTerm term
addBindOperators (x : xs) term =
  G.App bindOperator
    (toNonemptyList (G.PosArg argumentName : G.PosArg lambdaFun : []))
  where
    argumentName = getBinderName (addMonadicPrefixToBinder addOptionPrefix x)
    lambdaFun = G.Fun (singleton $ untypeBinder x) (addBindOperators xs term)

convertExprToTerm :: Exp l -> G.Term
convertExprToTerm (Var _ qName) =
  qNameToTerm qName
convertExprToTerm (Con _ qName) =
  qNameToTerm qName
convertExprToTerm (Paren _ expr) =
  G.Parens (convertExprToTerm expr)
convertExprToTerm (App _ expr1 expr2) =
  G.App (convertExprToTerm expr1) (singleton $ G.PosArg (convertExprToTerm expr2))
convertExprToTerm (InfixApp _ exprL (qOp) exprR) =
  (G.App (G.Qualid (qOpToQId qOp))
    ((G.PosArg (convertExprToTerm exprL)) B.:| (G.PosArg (convertExprToTerm exprR)) : []))
convertExprToTerm (Case _ expr altList) =
  G.Match (singleton $ G.MatchItem (convertExprToTerm expr)  Nothing Nothing)
    Nothing
      (convertAltListToEquationList altList)
convertExprToTerm _ =
  error "Haskell expression not implemented"


convertAltListToEquationList :: [Alt l] -> [G.Equation]
convertAltListToEquationList altList =
  [convertAltToEquation s | s <- altList]

convertAltToEquation :: Alt l -> G.Equation
convertAltToEquation (Alt _ pat rhs _) =
  G.Equation (singleton $ G.MultPattern (singleton $ convertHPatToGPat pat)) (convertRhsToTerm rhs)

convertHPatListToGPatList :: [Pat l] -> [G.Pattern]
convertHPatListToGPatList patList =
  [convertHPatToGPat s | s <- patList]

convertHPatToGPat :: Pat l -> G.Pattern
convertHPatToGPat (PVar _ name) =
  G.QualidPat (nameToQId name)
convertHPatToGPat (PApp _ qName pList) =
  G.ArgsPat (qNameToQId qName) (convertHPatListToGPatList pList)
convertHPatToGPat (PParen _ pat) =
  convertHPatToGPat pat
convertHPatToGPat (PWildCard _) =
  G.UnderscorePat
convertHPatToGPat _ =
  error "Haskell pattern not implemented"

convertQNameToBinder :: QName l -> G.Binder
convertQNameToBinder qName =
  G.Inferred G.Explicit (qNameToGName qName)

needsArgumentsSentence :: DeclHead l -> [QualConDecl l] -> Bool
needsArgumentsSentence declHead qConDecls =
  length binders > 0 && hasNonInferrableConstr qConDecls
  where
    binders = applyToDeclHeadTyVarBinds declHead convertTyVarBindToBinder

--check if function is recursive
isRecursive :: Name l -> Rhs l -> Bool
isRecursive name rhs =
  length (filter (== (getString name)) (termToStrings (convertRhsToTerm rhs))) > 0

--print the converted module
printCoqAST :: G.LocalModule -> IO ()
printCoqAST x =
  putDoc $ renderGallina x
