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


convertModule :: Module l -> ConversionMonad -> ConversionMode -> G.LocalModule
convertModule (Module _ (Just modHead) _ _ decls) cMonad cMode =
  G.LocalModule (convertModuleHead modHead)
    (monadDefinitions ++
      dataSentences ++
        (convertModuleDecls rDecls (map filterForTypeSignatures typeSigs) dataNames cMonad cMode))
  where
    (typeSigs, otherDecls) = partition isTypeSig decls
    (dataDecls, rDecls) = partition isDataDecl otherDecls
    dataSentences = convertModuleDecls dataDecls (map filterForTypeSignatures typeSigs) [] cMonad cMode
    dataNames = getNamesFromDataDecls dataDecls
convertModule (Module _ Nothing _ _ decls) cMonad cMode =
  G.LocalModule (T.pack "unnamed")
    (convertModuleDecls otherDecls  (map filterForTypeSignatures typeSigs) [] cMonad cMode)
  where
    (typeSigs, otherDecls) = partition isTypeSig decls

convertModuleHead :: ModuleHead l -> G.Ident
convertModuleHead (ModuleHead _ (ModuleName _ modName) _ _) =
  T.pack modName

--
convertModuleDecls :: [Decl l] -> [G.TypeSignature] -> [G.Name] -> ConversionMonad -> ConversionMode -> [G.Sentence]
convertModuleDecls ((FunBind _ (x : xs)) : ds) typeSigs dataNames cMonad cMode =
  convertMatchDef x typeSigs dataNames cMonad cMode : convertModuleDecls ds typeSigs dataNames cMonad cMode
convertModuleDecls ((DataDecl _ (DataType _ ) Nothing declHead qConDecl _ ) : ds) typeSigs dataNames cMonad cMode =
    if needsArgumentsSentence declHead qConDecl
      then [G.InductiveSentence  (convertDataTypeDecl declHead qConDecl cMonad)] ++
                                convertArgumentSentences declHead qConDecl ++
                                convertModuleDecls ds typeSigs dataNames cMonad cMode
      else G.InductiveSentence  (convertDataTypeDecl declHead qConDecl cMonad) :
                                convertModuleDecls ds typeSigs dataNames cMonad cMode
convertModuleDecls [] _ _ _ _=
  []
convertModuleDecls _ _ _ _ _=
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

convertDataTypeDecl :: DeclHead l -> [QualConDecl l] -> ConversionMonad -> G.Inductive
convertDataTypeDecl dHead qConDecl cMonad =
  G.Inductive (singleton $ G.IndBody typeName binders typeTerm constrDecls) []
    where
      typeName = applyToDeclHead dHead nameToQId
      binders = applyToDeclHeadTyVarBinds dHead convertTyVarBindToBinder
      constrDecls = convertQConDecls
                      qConDecl
                        (getReturnTypeFromDeclHead (applyToDeclHeadTyVarBinds dHead convertTyVarBindToArg) dHead)
                          cMonad

convertMatchDef :: Match l -> [G.TypeSignature] -> [G.Name] -> ConversionMonad -> ConversionMode -> G.Sentence
convertMatchDef (Match _ name pattern rhs _) typeSigs dataNames cMonad cMode =
    if isRecursive name rhs
      then G.FixpointSentence (convertMatchToFixpoint name pattern rhs typeSig dataNames cMonad cMode)
      else G.DefinitionSentence (convertMatchToDefinition name pattern rhs typeSig cMonad cMode)
    where
      typeSig = getTypeSignatureByName typeSigs name

convertMatchToDefinition :: Name l -> [Pat l] -> Rhs l -> Maybe G.TypeSignature -> ConversionMonad -> ConversionMode -> G.Definition
convertMatchToDefinition name pattern rhs typeSig cMonad cMode =
  G.DefinitionDef G.Global (nameToQId name)
    monadicBinders
      (convertReturnType typeSig cMonad)
        rhsTerm
  where
    monadicBinders = transformBindersMonadic (map (addMonadicPrefixToBinder cMonad) binders) cMonad
    binders = convertPatsToBinders pattern typeSig
    rhsTerm = addBindOperators binders (convertRhsToTerm rhs) Nothing cMonad cMode

convertMatchToFixpoint :: Name l -> [Pat l] -> Rhs l -> Maybe G.TypeSignature -> [G.Name] -> ConversionMonad -> ConversionMode -> G.Fixpoint
convertMatchToFixpoint name pattern rhs typeSig dataNames cMonad cMode =
  G.Fixpoint (singleton $ G.FixBody funName
    (toNonemptyList (bindersWithInferredTypes))
      Nothing
        Nothing
          rhsTerm) []
  where
    funName = nameToQId name
    binders = convertPatsToBinders pattern typeSig
    bindersWithFuel = addFuelBinder (transformBindersMonadic (map (addMonadicPrefixToBinder cMonad) binders) cMonad)
    bindersWithInferredTypes = addInferredTypesToSignature bindersWithFuel dataNames
    rhsTerm = addBindOperators binders (convertRhsToTerm rhs) (Just funName) cMonad cMode

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

convertQConDecls :: [QualConDecl l] -> G.Term -> ConversionMonad -> [(G.Qualid, [G.Binder], Maybe G.Term)]
convertQConDecls qConDecl term cMonad =
  [convertQConDecl c term cMonad | c <- qConDecl]

convertQConDecl :: QualConDecl l -> G.Term -> ConversionMonad -> (G.Qualid, [G.Binder], Maybe G.Term)
convertQConDecl (QualConDecl _ Nothing Nothing (ConDecl _ name types)) term cMonad =
  ((nameToQId name), [] , (Just (convertToArrowTerm types term cMonad)))

convertToArrowTerm :: [Type l] -> G.Term -> ConversionMonad -> G.Term
convertToArrowTerm types returnType cMonad =
  buildArrowTerm (map (convertTypeToMonadicTerm cMonad) types ) returnType

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

convertTypeToMonadicTerm :: ConversionMonad -> Type l -> G.Term
convertTypeToMonadicTerm cMonad (TyVar _ name)  =
  transformTermMonadic (nameToTypeTerm name) cMonad
convertTypeToMonadicTerm cMonad (TyCon _ qName)  =
  transformTermMonadic (qNameToTypeTerm qName) cMonad
convertTypeToMonadicTerm cMonad (TyParen _ ty)  =
  transformTermMonadic (G.Parens $ convertTypeToTerm ty) cMonad
convertTypeToMonadicTerm _ ty =
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

convertReturnType :: Maybe G.TypeSignature -> ConversionMonad -> Maybe G.Term
convertReturnType Nothing  _ =
  Nothing
convertReturnType (Just (G.TypeSignature _ types)) cMonad =
  Just (transformTermMonadic (last types) cMonad )

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


addBindOperators :: [G.Binder] -> G.Term -> Maybe G.Qualid -> ConversionMonad ->  ConversionMode -> G.Term
addBindOperators [] term (Just funName) cMonad cMode =
  toReturnTerm (addFuelMatchingToRhs term funName)
addBindOperators [] term Nothing cMonad cMode =
  toReturnTerm term
addBindOperators (x : xs) term funName cMonad cMode=
  G.App bindOperator
    (toNonemptyList (G.PosArg argumentName : G.PosArg lambdaFun : []))
  where
    argumentName = getBinderName (addMonadicPrefixToBinder cMonad x)
    lambdaFun = G.Fun (singleton $ untypeBinder x) (addBindOperators xs term funName cMonad cMode )

addFuelMatchingToRhs :: G.Term -> G.Qualid -> G.Term
addFuelMatchingToRhs (G.Match item retType equations) funName =
  G.Match item retType [addFuelMatchingToEquation e funName | e <- equations]
addFuelMatchingToRhs term funName =
  if containsRecursiveCall term funName
    then fuelPattern errorTerm term funName
    else term
  where
    errorTerm = G.Qualid (strToQId "ys") -- placeHolder!works only for append Change to return term in errorcase

addFuelMatchingToEquation :: G.Equation -> G.Qualid -> G.Equation
addFuelMatchingToEquation (G.Equation multPattern rhs) funName =
  G.Equation multPattern (addFuelMatchingToRhs rhs funName)


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
