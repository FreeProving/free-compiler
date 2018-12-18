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


convertModule :: Show l => Module l -> ConversionMonad -> ConversionMode -> G.LocalModule
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

convertModuleHead :: Show l => ModuleHead l -> G.Ident
convertModuleHead (ModuleHead _ (ModuleName _ modName) _ _) =
  T.pack modName

--
convertModuleDecls :: Show l => [Decl l] -> [G.TypeSignature] -> [G.Name] -> ConversionMonad -> ConversionMode -> [G.Sentence]
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
convertModuleDecls (d : ds) _ _ _ _=
   error ("Top-level declaration not implemented: " ++ show d)


convertArgumentSentences :: Show l => DeclHead l -> [QualConDecl l] -> [G.Sentence]
convertArgumentSentences declHead qConDecls =
  [G.ArgumentsSentence (G.Arguments Nothing con (convertArgumentSpec declHead)) | con <- constrToDefine]
  where
    constrToDefine = getNonInferrableConstrNames qConDecls

convertArgumentSpec :: Show l => DeclHead l -> [G.ArgumentSpec]
convertArgumentSpec declHead =
  [G.ArgumentSpec G.ArgMaximal varName Nothing | varName <- varNames]
  where
   varNames = applyToDeclHeadTyVarBinds declHead convertTyVarBindToName

convertDataTypeDecl :: Show l => DeclHead l -> [QualConDecl l] -> ConversionMonad -> G.Inductive
convertDataTypeDecl dHead qConDecl cMonad =
  G.Inductive (singleton $ G.IndBody typeName binders typeTerm constrDecls) []
    where
      typeName = applyToDeclHead dHead nameToQId
      binders = applyToDeclHeadTyVarBinds dHead convertTyVarBindToBinder
      constrDecls = convertQConDecls
                      qConDecl
                        (getReturnTypeFromDeclHead (applyToDeclHeadTyVarBinds dHead convertTyVarBindToArg) dHead)
                          cMonad

convertMatchDef :: Show l => Match l -> [G.TypeSignature] -> [G.Name] -> ConversionMonad -> ConversionMode -> G.Sentence
convertMatchDef (Match _ name pattern rhs _) typeSigs dataNames cMonad cMode =
    if isRecursive name rhs
      then if cMode == FueledFunction
            then G.FixpointSentence (convertMatchToFueledFixpoint name pattern rhs typeSig dataNames cMonad)
            else error "HelperFunction Conversion not implemented"
      else G.DefinitionSentence (convertMatchToDefinition name pattern rhs typeSig cMonad)
    where
      typeSig = getTypeSignatureByName typeSigs name

convertMatchToDefinition :: Show l => Name l -> [Pat l] -> Rhs l -> Maybe G.TypeSignature -> ConversionMonad -> G.Definition
convertMatchToDefinition name pattern rhs typeSig cMonad =
  G.DefinitionDef G.Global (nameToQId name)
    monadicBinders
      (convertReturnType typeSig cMonad)
        rhsTerm
  where
    binders = convertPatsToBinders pattern typeSig
    monadicBinders = transformBindersMonadic (map (addMonadicPrefixToBinder cMonad) binders) cMonad
    rhsTerm = addBindOperators monadicBinders (convertRhsToTerm rhs)

convertMatchToFueledFixpoint :: Show l => Name l -> [Pat l] -> Rhs l -> Maybe G.TypeSignature -> [G.Name] -> ConversionMonad -> G.Fixpoint
convertMatchToFueledFixpoint name pattern rhs (Just typeSig) dataNames cMonad =
 G.Fixpoint (singleton $ G.FixBody funName
    (toNonemptyList (bindersWithInferredTypes))
      Nothing
        Nothing
          fueledRhs) []
  where
    funName = nameToQId name
    binders = convertPatsToBinders pattern (Just typeSig)
    monadicBinders = transformBindersMonadic (map (addMonadicPrefixToBinder cMonad) binders) cMonad
    bindersWithFuel = addFuelBinder monadicBinders
    bindersWithInferredTypes = addInferredTypesToSignature bindersWithFuel dataNames
    rhsTerm = addBindOperators monadicBinders (convertRhsToTerm rhs)
    fueledRhs = addFuelMatchingToRhs rhsTerm monadicBinders [] funName (getReturnType typeSig)

getReturnTypeFromDeclHead :: [G.Arg] -> DeclHead l -> G.Term
getReturnTypeFromDeclHead [] dHead =
  applyToDeclHead dHead nameToTerm
getReturnTypeFromDeclHead (x : xs) dHead =
  G.App (applyToDeclHead dHead nameToTerm) (x B.:| xs)

convertTyVarBindToName :: Show l => TyVarBind l -> G.Name
convertTyVarBindToName (KindedVar _ name _) =
  nameToGName name
convertTyVarBindToName (UnkindedVar _ name) =
  nameToGName name

convertTyVarBindToBinder :: Show l => TyVarBind l -> G.Binder
convertTyVarBindToBinder (KindedVar _ name kind) =
  error "Kind-annotation not implemented"
convertTyVarBindToBinder (UnkindedVar _ name) =
  G.Typed G.Ungeneralizable G.Explicit (singleton $ nameToGName name) typeTerm

convertTyVarBindToArg :: Show l => TyVarBind l -> G.Arg
convertTyVarBindToArg (KindedVar _ name kind) =
  error "Kind-annotation not implemented"
convertTyVarBindToArg (UnkindedVar _ name) =
  G.PosArg (nameToTerm name)

convertQConDecls :: Show l => [QualConDecl l] -> G.Term -> ConversionMonad -> [(G.Qualid, [G.Binder], Maybe G.Term)]
convertQConDecls qConDecl term cMonad =
  [convertQConDecl c term cMonad | c <- qConDecl]

convertQConDecl :: Show l => QualConDecl l -> G.Term -> ConversionMonad -> (G.Qualid, [G.Binder], Maybe G.Term)
convertQConDecl (QualConDecl _ Nothing Nothing (ConDecl _ name types)) term cMonad =
  ((nameToQId name), [] , (Just (convertToArrowTerm types term cMonad)))

convertToArrowTerm :: Show l => [Type l] -> G.Term -> ConversionMonad -> G.Term
convertToArrowTerm types returnType cMonad =
  buildArrowTerm (map (convertTypeToMonadicTerm cMonad) types ) returnType

buildArrowTerm :: [G.Term] -> G.Term -> G.Term
buildArrowTerm terms returnType =
  foldr G.Arrow returnType terms

filterForTypeSignatures :: Show l => Decl l -> G.TypeSignature
filterForTypeSignatures (TypeSig _ (name : rest) types) =
  G.TypeSignature (nameToGName name)
    (convertTypeToTerms types)

convertTypeToArg :: Show l => Type l -> G.Arg
convertTypeToArg ty =
  G.PosArg (convertTypeToTerm ty)

convertTypeToMonadicTerm :: Show l => ConversionMonad -> Type l -> G.Term
convertTypeToMonadicTerm cMonad (TyVar _ name)  =
  transformTermMonadic (nameToTypeTerm name) cMonad
convertTypeToMonadicTerm cMonad (TyCon _ qName)  =
  transformTermMonadic (qNameToTypeTerm qName) cMonad
convertTypeToMonadicTerm cMonad (TyParen _ ty)  =
  transformTermMonadic (G.Parens $ convertTypeToTerm ty) cMonad
convertTypeToMonadicTerm _ ty =
  convertTypeToTerm ty

convertTypeToTerm :: Show l => Type l -> G.Term
convertTypeToTerm (TyVar _ name) =
  nameToTypeTerm name
convertTypeToTerm (TyCon _ qName) =
  qNameToTypeTerm qName
convertTypeToTerm (TyParen _ ty) =
  G.Parens (convertTypeToTerm ty)
convertTypeToTerm (TyApp _ type1 type2) =
  G.App (convertTypeToTerm type1) (singleton $ convertTypeToArg type2)
convertTypeToTerm ty =
  error ("Haskell-type not implemented: " ++ show ty )

convertTypeToTerms :: Show l => Type l -> [G.Term]
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

convertPatsToBinders :: Show l => [Pat l] -> Maybe G.TypeSignature -> [G.Binder]
convertPatsToBinders patList Nothing =
  [convertPatToBinder p | p <- patList]
convertPatsToBinders patList (Just (G.TypeSignature _ typeList)) =
  convertPatsAndTypeSigsToBinders patList (init typeList)

convertPatToBinder :: Show l => Pat l -> G.Binder
convertPatToBinder (PVar _ name) =
  G.Inferred G.Explicit (nameToGName name)
convertPatToBinder pat =
  error ("Pattern not implemented: " ++ show pat)

convertPatsAndTypeSigsToBinders :: Show l => [Pat l] -> [G.Term] -> [G.Binder]
convertPatsAndTypeSigsToBinders pats typeSigs =
  zipWith convertPatAndTypeSigToBinder pats typeSigs

convertPatAndTypeSigToBinder :: Show l => Pat l -> G.Term -> G.Binder
convertPatAndTypeSigToBinder (PVar _ name) term =
  G.Typed G.Ungeneralizable G.Explicit (singleton $ nameToGName name) term
convertPatAndTypeSigToBinder pat _ =
  error ("Haskell pattern not implemented: " ++ show pat)

addInferredTypesToSignature :: [G.Binder] -> [G.Name] -> [G.Binder]
addInferredTypesToSignature binders dataNames =
  if null filteredTypeNames
    then binders
    else (G.Typed G.Ungeneralizable G.Explicit (toNonemptyList (filteredTypeNames)) typeTerm) : binders
  where
    filteredTypeNames = unique $ filterEachElement dataNames dataTypeUneqGName (filter isCoqType typeNames)
    typeNames = concat (map getTypeNamesFromTerm typeTerms)
    typeTerms = map getBinderType binders
    consNames = unique (map getConstrNameFromType typeTerms)

convertRhsToTerm :: Show l => Rhs l -> G.Term
convertRhsToTerm (UnGuardedRhs _ expr) =
  collapseApp (convertExprToTerm expr)
convertRhsToTerm (GuardedRhss _ _ ) =
  error "Guards not implemented"


addBindOperators :: [G.Binder] -> G.Term -> G.Term
addBindOperators [] term =
  toReturnTerm term
addBindOperators (x : xs) term =
  G.App bindOperator
    (toNonemptyList (G.PosArg argumentName : G.PosArg lambdaFun : []))
  where
    argumentName = getBinderName x
    lambdaFun = G.Fun (singleton $ removeMonadFromBinder x) (addBindOperators xs term )

addFuelMatchingToRhs :: G.Term -> [G.Binder] -> [G.Binder] -> G.Qualid -> G.Term -> G.Term
addFuelMatchingToRhs (G.Match item rType equations) funBinders lambdaBinders funName retType =
  G.Match item rType [addFuelMatchingToEquation e funBinders lambdaBinders funName retType | e <- equations]
addFuelMatchingToRhs term funBinders lambdaBinders funName retType =
  if containsRecursiveCall term funName
    then fuelPattern errorTerm recursiveCall funName
    else case term of
      G.App returnOp (b B.:| []) -> G.App returnOp (singleton $ G.PosArg (addFuelMatchingToRhs
                                                                  ((\(G.PosArg x) -> x ) (b))
                                                                    funBinders
                                                                      lambdaBinders
                                                                        funName
                                                                          retType))
      G.App bindOp (b B.:| bs) -> G.App bindOp (toNonemptyList (b :
                                        G.PosArg (addFuelMatchingToRhs
                                          ((\(G.PosArg x) -> x ) (head bs))
                                            funBinders
                                              lambdaBinders
                                                funName
                                                  retType) : []))
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
containsWrongArgument (G.PosArg (G.Qualid qId)) lambdaBinders =
  not (null (filter (qIdEqBinder qId) lambdaBinders))

switchArgument :: Int -> [G.Binder] -> G.Arg
switchArgument n funBinders =
  binderToArg bind
  where
    bind = funBinders !! (((length funBinders) - n) - 1)

convertExprToTerm :: Show l => Exp l -> G.Term
convertExprToTerm (Var _ qName) =
  qNameToTerm qName
convertExprToTerm (Con _ qName) =
  qNameToTerm qName
convertExprToTerm (Paren _ expr) =
  G.Parens (convertExprToTerm expr)
convertExprToTerm (App _ expr1 expr2) =
  G.App (convertExprToTerm expr1) (singleton $ G.PosArg $ convertExprToTerm expr2)
convertExprToTerm (InfixApp _ exprL (qOp) exprR) =
  (G.App (G.Qualid (qOpToQId qOp))
    ((G.PosArg (convertExprToTerm exprL)) B.:| (G.PosArg (convertExprToTerm exprR)) : []))
convertExprToTerm (Case _ expr altList) =
  G.Match (singleton $ G.MatchItem (convertExprToTerm expr)  Nothing Nothing)
    Nothing
      (convertAltListToEquationList altList)
convertExprToTerm expr =
  error ("Haskell expression not implemented: " ++ show expr)


convertAltListToEquationList :: Show l => [Alt l] -> [G.Equation]
convertAltListToEquationList altList =
  [convertAltToEquation s | s <- altList]

convertAltToEquation :: Show l => Alt l -> G.Equation
convertAltToEquation (Alt _ pat rhs _) =
  G.Equation (singleton $ G.MultPattern (singleton $ convertHPatToGPat pat)) (convertRhsToTerm rhs)

convertHPatListToGPatList :: Show l => [Pat l] -> [G.Pattern]
convertHPatListToGPatList patList =
  [convertHPatToGPat s | s <- patList]

convertHPatToGPat :: Show l => Pat l -> G.Pattern
convertHPatToGPat (PVar _ name) =
  G.QualidPat (nameToQId name)
convertHPatToGPat (PApp _ qName pList) =
  G.ArgsPat (qNameToQId qName) (convertHPatListToGPatList pList)
convertHPatToGPat (PParen _ pat) =
  convertHPatToGPat pat
convertHPatToGPat (PWildCard _) =
  G.UnderscorePat
convertHPatToGPat pat =
  error ("Haskell pattern not implemented: " ++ show pat)

convertQNameToBinder :: Show l => QName l -> G.Binder
convertQNameToBinder qName =
  G.Inferred G.Explicit (qNameToGName qName)

needsArgumentsSentence :: Show l => DeclHead l -> [QualConDecl l] -> Bool
needsArgumentsSentence declHead qConDecls =
  length binders > 0 && hasNonInferrableConstr qConDecls
  where
    binders = applyToDeclHeadTyVarBinds declHead convertTyVarBindToBinder

--check if function is recursive
isRecursive :: Show l => Name l -> Rhs l -> Bool
isRecursive name rhs =
  length (filter (== (getString name)) (termToStrings (convertRhsToTerm rhs))) > 0

--print the converted module
printCoqAST :: G.LocalModule -> IO ()
printCoqAST x =
  putDoc $ renderGallina x
