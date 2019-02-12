module Compiler.Converter where

import qualified Language.Coq.Gallina as G
import Language.Coq.Pretty (renderGallina)
import qualified Language.Haskell.Exts.Syntax as H
import Text.PrettyPrint.Leijen.Text (displayT, renderPretty)

import Compiler.FueledFunctions
  ( addFuelArgToRecursiveCalls
  , addFuelBinder
  , addFuelMatching
  , convertFueledFunBody
  , fuelTerm
  )
import Compiler.HelperFunctionConverter (convertMatchToHelperFunction, convertMatchToMainFunction)
import Compiler.HelperFunctions
  ( addInferredTypesToSignature
  , applyToDeclHead
  , applyToDeclHeadTyVarBinds
  , collapseApp
  , containsRecursiveCall
  , gNameToQId
  , getConstrNamesFromDataDecls
  , getInferredBindersFromRetType
  , getNameFromDeclHead
  , getNamesFromDataDecls
  , getNonInferrableConstrNames
  , getReturnType
  , getReturnTypeFromDeclHead
  , getString
  , getTypeSignatureByName
  , getTypeSignatureByQId
  , hasNonInferrableConstr
  , isDataDecl
  , isSpecialConstr
  , isSpecialOperator
  , isTypeSig
  , listTerm
  , nameToGName
  , nameToQId
  , nameToTerm
  , nameToTypeTerm
  , pairTerm
  , patToQID
  , qNameToQId
  , qNameToTerm
  , qNameToText
  , qNameToTypeTerm
  , qOpToQId
  , qOpToQOpId
  , strToGName
  , strToQId
  , termToStrings
  , typeTerm
  )
import Compiler.MonadicConverter
  ( addBindOperatorsToDefinition
  , addReturnToRhs
  , transformBindersMonadic
  , transformTermMonadic
  )
import Compiler.NonEmptyList (singleton, toNonemptyList)
import Compiler.Types (ConversionMode(..), ConversionMonad(..))

import qualified GHC.Base as B

import Data.List (partition)
import Data.Maybe (fromJust)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Text.PrettyPrint.Leijen.Text (displayT, renderPretty)

convertModule :: Show l => H.Module l -> ConversionMonad -> ConversionMode -> G.Sentence
convertModule (H.Module _ (Just modHead) _ _ decls) cMonad cMode =
  G.LocalModuleSentence
    (G.LocalModule
       (convertModuleHead modHead)
       (dataSentences ++ convertModuleDecls rDecls (map filterForTypeSignatures typeSigs) dataTypes funs cMonad cMode))
  where
    (typeSigs, otherDecls) = partition isTypeSig decls
    (dataDecls, rDecls) = partition isDataDecl otherDecls
    dataSentences = convertModuleDecls dataDecls (map filterForTypeSignatures typeSigs) [] funs cMonad cMode
    dataTypes = predefinedDataTypes ++ zip (getNamesFromDataDecls dataDecls) (getConstrNamesFromDataDecls dataDecls)
    funs = getFunNames rDecls
convertModule (H.Module _ Nothing _ _ decls) cMonad cMode =
  G.LocalModuleSentence
    (G.LocalModule
       (T.pack "unnamed")
       (convertModuleDecls otherDecls (map filterForTypeSignatures typeSigs) [] funs cMonad cMode))
  where
    (typeSigs, otherDecls) = partition isTypeSig decls
    funs = getFunNames otherDecls

----------------------------------------------------------------------------------------------------------------------
getFunNames :: Show l => [H.Decl l] -> [G.Qualid]
getFunNames decls = map getQIdFromFunDecl (filter isFunction decls)

isFunction :: Show l => H.Decl l -> Bool
isFunction (H.FunBind _ _) = True
isFunction _ = False

getQIdFromFunDecl :: Show l => H.Decl l -> G.Qualid
getQIdFromFunDecl (H.FunBind _ (H.Match _ name _ _ _:_)) = nameToQId name

convertModuleHead :: Show l => H.ModuleHead l -> G.Ident
convertModuleHead (H.ModuleHead _ (H.ModuleName _ modName) _ _) = T.pack modName

importDefinitions :: [G.Sentence]
importDefinitions = [stringImport, libraryImport, monadImport]
  where
    stringImport = G.ModuleSentence (G.Require Nothing (Just G.Import) (singleton (T.pack "String")))
    libraryImport = G.ModuleSentence (G.Require Nothing (Just G.Import) (singleton (T.pack "ImportModules")))
    monadImport = G.ModuleSentence (G.ModuleImport G.Import (singleton (T.pack "Monad")))

convertModuleDecls ::
     Show l
  => [H.Decl l]
  -> [G.TypeSignature]
  -> [(G.Name, [G.Qualid])]
  -> [G.Qualid]
  -> ConversionMonad
  -> ConversionMode
  -> [G.Sentence]
convertModuleDecls (H.FunBind _ (x:xs):ds) typeSigs dataTypes funs cMonad cMode =
  convertMatchDef x typeSigs dataTypes funs cMonad cMode ++ convertModuleDecls ds typeSigs dataTypes funs cMonad cMode
convertModuleDecls (H.DataDecl _ (H.DataType _) Nothing declHead qConDecl _:ds) typeSigs dataTypes funs cMonad cMode =
  if needsArgumentsSentence declHead qConDecl
    then [G.InductiveSentence (convertDataTypeDecl declHead qConDecl cMonad)] ++
         convertArgumentSentences declHead qConDecl ++ convertModuleDecls ds typeSigs dataTypes funs cMonad cMode
    else G.InductiveSentence (convertDataTypeDecl declHead qConDecl cMonad) :
         convertModuleDecls ds typeSigs dataTypes funs cMonad cMode
convertModuleDecls (H.TypeDecl _ declHead ty:ds) typeSigs dataTypes funs cMonad cMode =
  G.DefinitionSentence (convertTypeDeclToDefinition declHead ty) :
  convertModuleDecls ds typeSigs dataTypes funs cMonad cMode
convertModuleDecls (H.PatBind _ pat rhs _:ds) typeSigs dataTypes funs cMonad cMode =
  G.DefinitionSentence (convertPatBindToDefinition pat rhs typeSigs dataTypes cMonad) :
  convertModuleDecls ds typeSigs dataTypes funs cMonad cMode
convertModuleDecls [] _ _ _ _ _ = []
convertModuleDecls (d:ds) _ _ _ _ _ = error ("Top-level declaration not implemented: " ++ show d)

convertTypeDeclToDefinition :: Show l => H.DeclHead l -> H.Type l -> G.Definition
convertTypeDeclToDefinition dHead ty = G.DefinitionDef G.Global name binders Nothing rhs
  where
    name = (gNameToQId . getNameFromDeclHead) dHead
    binders = applyToDeclHeadTyVarBinds dHead convertTyVarBindToBinder
    rhs = convertTypeToTerm ty

convertPatBindToDefinition ::
     Show l => H.Pat l -> H.Rhs l -> [G.TypeSignature] -> [(G.Name, [G.Qualid])] -> ConversionMonad -> G.Definition
convertPatBindToDefinition pat rhs typeSigs dataTypes cMonad = G.DefinitionDef G.Global name binders returnType rhsTerm
  where
    dataNames = map fst dataTypes
    binders = getInferredBindersFromRetType (fromJust returnType)
    name = patToQID pat
    typeSig = getTypeSignatureByQId typeSigs name
    returnType = convertReturnType typeSig cMonad
    rhsTerm = addReturnToRhs (convertRhsToTerm rhs) [] [] [] cMonad

convertArgumentSentences :: Show l => H.DeclHead l -> [H.QualConDecl l] -> [G.Sentence]
convertArgumentSentences declHead qConDecls =
  [G.ArgumentsSentence (G.Arguments Nothing con (convertArgumentSpec declHead)) | con <- constrToDefine]
  where
    constrToDefine = getNonInferrableConstrNames qConDecls

convertArgumentSpec :: Show l => H.DeclHead l -> [G.ArgumentSpec]
convertArgumentSpec declHead = [G.ArgumentSpec G.ArgMaximal varName Nothing | varName <- varNames]
  where
    varNames = applyToDeclHeadTyVarBinds declHead convertTyVarBindToName

convertDataTypeDecl :: Show l => H.DeclHead l -> [H.QualConDecl l] -> ConversionMonad -> G.Inductive
convertDataTypeDecl dHead qConDecl cMonad = G.Inductive (singleton (G.IndBody typeName binders typeTerm constrDecls)) []
  where
    typeName = applyToDeclHead dHead nameToQId
    binders = applyToDeclHeadTyVarBinds dHead convertTyVarBindToBinder
    constrDecls =
      convertQConDecls
        qConDecl
        (getReturnTypeFromDeclHead (applyToDeclHeadTyVarBinds dHead convertTyVarBindToArg) dHead)
        cMonad

convertMatchDef ::
     Show l
  => H.Match l
  -> [G.TypeSignature]
  -> [(G.Name, [G.Qualid])]
  -> [G.Qualid]
  -> ConversionMonad
  -> ConversionMode
  -> [G.Sentence]
convertMatchDef (H.Match _ name mPats rhs _) typeSigs dataTypes funs cMonad cMode =
  if containsRecursiveCall rhsTerm funName
    then if cMode == FueledFunction
           then [G.FixpointSentence (convertMatchToFueledFixpoint name mPats rhs typeSigs dataTypes funs cMonad)]
           else convertMatchWithHelperFunction name mPats rhs typeSigs dataTypes cMonad
    else [G.DefinitionSentence (convertMatchToDefinition name mPats rhs typeSigs dataTypes funs cMonad cMode)]
  where
    rhsTerm = convertRhsToTerm rhs
    funName = nameToQId name

convertMatchToDefinition ::
     Show l
  => H.Name l
  -> [H.Pat l]
  -> H.Rhs l
  -> [G.TypeSignature]
  -> [(G.Name, [G.Qualid])]
  -> [G.Qualid]
  -> ConversionMonad
  -> ConversionMode
  -> G.Definition
convertMatchToDefinition name pats rhs typeSigs dataTypes funs cMonad cMode =
  if cMode == FueledFunction
    then if (not . null) funCalls
           then G.DefinitionDef G.Global funName bindersWithFuel returnType fueledMonadicTerm
           else G.DefinitionDef G.Global funName bindersWithFuel returnType monadicTerm
    else G.DefinitionDef G.Global funName bindersWithInferredTypes returnType monadicTerm
  where
    returnType = convertReturnType typeSig cMonad
    funName = nameToQId name
    funCalls = filter (containsRecursiveCall rhsTerm) funs
    typeSig = getTypeSignatureByName typeSigs name
    binders = convertPatsToBinders pats typeSig
    monadicBinders = transformBindersMonadic binders cMonad
    bindersWithInferredTypes = addInferredTypesToSignature monadicBinders (map fst dataTypes)
    bindersWithFuel = addFuelBinder bindersWithInferredTypes
    rhsTerm = convertRhsToTerm rhs
    monadicTerm = addBindOperatorsToDefinition monadicBinders (addReturnToRhs rhsTerm typeSigs monadicBinders dataTypes cMonad) cMonad
    fueledTerm = addFuelArgToRecursiveCalls rhsTerm fuelTerm funCalls
    fueledMonadicTerm =
      addBindOperatorsToDefinition monadicBinders (addReturnToRhs fueledTerm typeSigs monadicBinders dataTypes cMonad) cMonad

convertMatchToFueledFixpoint ::
     Show l
  => H.Name l
  -> [H.Pat l]
  -> H.Rhs l
  -> [G.TypeSignature]
  -> [(G.Name, [G.Qualid])]
  -> [G.Qualid]
  -> ConversionMonad
  -> G.Fixpoint
convertMatchToFueledFixpoint name pats rhs typeSigs dataTypes funs cMonad =
  G.Fixpoint
    (singleton
       (G.FixBody
          funName
          (toNonemptyList bindersWithFuel)
          Nothing
          (Just (transformTermMonadic (getReturnType typeSig) cMonad))
          fueledRhs))
    []
  where
    typeSig = fromJust (getTypeSignatureByName typeSigs name)
    funName = nameToQId name
    binders = convertPatsToBinders pats (Just typeSig)
    monadicBinders = transformBindersMonadic binders cMonad
    bindersWithFuel = addFuelBinder bindersWithInferredTypes
    bindersWithInferredTypes = addInferredTypesToSignature monadicBinders (map fst dataTypes)
    rhsTerm = convertRhsToTerm rhs
    convertedFunBody =
      convertFueledFunBody
        (addReturnToRhs rhsTerm typeSigs monadicBinders dataTypes cMonad)
        monadicBinders
        funName
        typeSigs
        funs
    fueledRhs = addFuelMatching monadicRhs funName
    monadicRhs = addBindOperatorsToDefinition monadicBinders convertedFunBody cMonad

convertMatchWithHelperFunction ::
     Show l
  => H.Name l
  -> [H.Pat l]
  -> H.Rhs l
  -> [G.TypeSignature]
  -> [(G.Name, [G.Qualid])]
  -> ConversionMonad
  -> [G.Sentence]
convertMatchWithHelperFunction name pats rhs typeSigs dataTypes cMonad =
  [ G.FixpointSentence (convertMatchToMainFunction name binders rhsTerm typeSigs dataTypes cMonad)
  , G.DefinitionSentence (convertMatchToHelperFunction name binders rhsTerm typeSigs dataTypes cMonad)
  ]
  where
    rhsTerm = convertRhsToTerm rhs
    binders = convertPatsToBinders pats typeSig
    typeSig = getTypeSignatureByName typeSigs name

convertTyVarBindToName :: Show l => H.TyVarBind l -> G.Name
convertTyVarBindToName (H.KindedVar _ name _) = nameToGName name
convertTyVarBindToName (H.UnkindedVar _ name) = nameToGName name

convertTyVarBindToBinder :: Show l => H.TyVarBind l -> G.Binder
convertTyVarBindToBinder (H.KindedVar _ name kind) = error "Kind-annotation not implemented"
convertTyVarBindToBinder (H.UnkindedVar _ name) =
  G.Typed G.Ungeneralizable G.Explicit (singleton (nameToGName name)) typeTerm

convertTyVarBindToArg :: Show l => H.TyVarBind l -> G.Arg
convertTyVarBindToArg (H.KindedVar _ name kind) = error "Kind-annotation not implemented"
convertTyVarBindToArg (H.UnkindedVar _ name) = G.PosArg (nameToTerm name)

convertQConDecls :: Show l => [H.QualConDecl l] -> G.Term -> ConversionMonad -> [(G.Qualid, [G.Binder], Maybe G.Term)]
convertQConDecls qConDecl term cMonad = [convertQConDecl c term cMonad | c <- qConDecl]

convertQConDecl :: Show l => H.QualConDecl l -> G.Term -> ConversionMonad -> (G.Qualid, [G.Binder], Maybe G.Term)
convertQConDecl (H.QualConDecl _ Nothing Nothing (H.ConDecl _ name types)) term cMonad =
  (nameToQId name, [], Just (convertToArrowTerm types term cMonad))

convertToArrowTerm :: Show l => [H.Type l] -> G.Term -> ConversionMonad -> G.Term
convertToArrowTerm types returnType cMonad = buildArrowTerm (map (convertTypeToMonadicTerm cMonad) types) returnType

buildArrowTerm :: [G.Term] -> G.Term -> G.Term
buildArrowTerm terms returnType = foldr G.Arrow returnType terms

filterForTypeSignatures :: Show l => H.Decl l -> G.TypeSignature
filterForTypeSignatures (H.TypeSig _ (name:rest) types) = G.TypeSignature (nameToGName name) (convertTypeToTerms types)

convertTypeToArg :: Show l => H.Type l -> G.Arg
convertTypeToArg ty = G.PosArg (convertTypeToTerm ty)

convertTypeToMonadicTerm :: Show l => ConversionMonad -> H.Type l -> G.Term
convertTypeToMonadicTerm cMonad (H.TyVar _ name) = transformTermMonadic (nameToTypeTerm name) cMonad
convertTypeToMonadicTerm cMonad (H.TyCon _ qName) = transformTermMonadic (qNameToTypeTerm qName) cMonad
convertTypeToMonadicTerm cMonad (H.TyParen _ ty) = transformTermMonadic (G.Parens (convertTypeToTerm ty)) cMonad
convertTypeToMonadicTerm _ ty = convertTypeToTerm ty

convertTypeToTerm :: Show l => H.Type l -> G.Term
convertTypeToTerm (H.TyVar _ name) = nameToTypeTerm name
convertTypeToTerm (H.TyCon _ qName) = qNameToTypeTerm qName
convertTypeToTerm (H.TyParen _ ty) = G.Parens (convertTypeToTerm ty)
convertTypeToTerm (H.TyApp _ type1 type2) = G.App (convertTypeToTerm type1) (singleton (convertTypeToArg type2))
convertTypeToTerm (H.TyList _ ty) = G.App listTerm (singleton (G.PosArg (convertTypeToTerm ty)))
convertTypeToTerm (H.TyTuple _ _ tys) = G.App pairTerm (toNonemptyList [convertTypeToArg t | t <- tys])
convertTypeToTerm ty = error ("Haskell-type not implemented: " ++ show ty)

convertTypeToTerms :: Show l => H.Type l -> [G.Term]
convertTypeToTerms (H.TyFun _ type1 type2) = convertTypeToTerms type1 ++ convertTypeToTerms type2
convertTypeToTerms t = [convertTypeToTerm t]

convertReturnType :: Maybe G.TypeSignature -> ConversionMonad -> Maybe G.Term
convertReturnType Nothing _ = Nothing
convertReturnType (Just (G.TypeSignature _ types)) cMonad = Just (transformTermMonadic (last types) cMonad)

convertPatsToBinders :: Show l => [H.Pat l] -> Maybe G.TypeSignature -> [G.Binder]
convertPatsToBinders patList Nothing = [convertPatToBinder p | p <- patList]
convertPatsToBinders patList (Just (G.TypeSignature _ typeList)) =
  convertPatsAndTypeSigsToBinders patList (init typeList)

convertPatToBinder :: Show l => H.Pat l -> G.Binder
convertPatToBinder (H.PVar _ name) = G.Inferred G.Explicit (nameToGName name)
convertPatToBinder pat = error ("Pattern not implemented: " ++ show pat)

convertPatsAndTypeSigsToBinders :: Show l => [H.Pat l] -> [G.Term] -> [G.Binder]
convertPatsAndTypeSigsToBinders = zipWith convertPatAndTypeSigToBinder

convertPatAndTypeSigToBinder :: Show l => H.Pat l -> G.Term -> G.Binder
convertPatAndTypeSigToBinder (H.PVar _ name) term =
  G.Typed G.Ungeneralizable G.Explicit (singleton (nameToGName name)) term
convertPatAndTypeSigToBinder pat _ = error ("Haskell pattern not implemented: " ++ show pat)

convertRhsToTerm :: Show l => H.Rhs l -> G.Term
convertRhsToTerm (H.UnGuardedRhs _ expr) = collapseApp (convertExprToTerm expr)
convertRhsToTerm (H.GuardedRhss _ _) = error "Guards not implemented"

convertExprToTerm :: Show l => H.Exp l -> G.Term
convertExprToTerm (H.Var _ qName) = qNameToTerm qName
convertExprToTerm (H.Con _ qName) = qNameToTerm qName
convertExprToTerm (H.Paren _ expr) = G.Parens (convertExprToTerm expr)
convertExprToTerm (H.App _ expr1 expr2) =
  G.App ((collapseApp . convertExprToTerm) expr1) (singleton (G.PosArg ((collapseApp . convertExprToTerm) expr2)))
convertExprToTerm (H.InfixApp _ exprL qOp exprR) =
  if isSpecialOperator qOp
    then G.App
           (G.Qualid (qOpToQId qOp))
           (toNonemptyList
              [G.PosArg ((collapseApp . convertExprToTerm) exprL), G.PosArg ((collapseApp . convertExprToTerm) exprR)])
    else G.App
           (G.Qualid (qOpToQOpId qOp))
           (toNonemptyList
              [G.PosArg ((collapseApp . convertExprToTerm) exprL), G.PosArg ((collapseApp . convertExprToTerm) exprR)])
convertExprToTerm (H.Case _ expr altList) =
  G.Match
    (singleton (G.MatchItem (convertExprToTerm expr) Nothing Nothing))
    Nothing
    (convertAltListToEquationList altList)
convertExprToTerm (H.Lit _ literal) = convertLiteralToTerm literal
convertExprToTerm (H.Tuple _ _ exprs) =
  G.App (G.Qualid (strToQId "P")) (toNonemptyList [(G.PosArg . convertExprToTerm) e | e <- exprs])
convertExprToTerm (H.List _ []) = G.Qualid (strToQId "Nil")
convertExprToTerm expr = error ("Haskell expression not implemented: " ++ show expr)

convertLiteralToTerm :: Show l => H.Literal l -> G.Term
convertLiteralToTerm (H.Char _ char _) = G.HsChar char
convertLiteralToTerm (H.String _ str _) = G.String (T.pack str)
convertLiteralToTerm (H.Int _ _ int) = G.Qualid (strToQId int)
convertLiteralToTerm literal = error ("Haskell Literal not implemented: " ++ show literal)

convertAltListToEquationList :: Show l => [H.Alt l] -> [G.Equation]
convertAltListToEquationList altList = [convertAltToEquation s | s <- altList]

convertAltToEquation :: Show l => H.Alt l -> G.Equation
convertAltToEquation (H.Alt _ pat rhs _) =
  G.Equation (singleton (G.MultPattern (singleton (convertHPatToGPat pat)))) (convertRhsToTerm rhs)

convertHPatListToGPatList :: Show l => [H.Pat l] -> [G.Pattern]
convertHPatListToGPatList patList = [convertHPatToGPat s | s <- patList]

convertHPatToGPat :: Show l => H.Pat l -> G.Pattern
convertHPatToGPat (H.PVar _ name) = G.QualidPat (nameToQId name)
convertHPatToGPat (H.PApp _ qName pList) = G.ArgsPat (qNameToQId qName) (convertHPatListToGPatList pList)
convertHPatToGPat (H.PParen _ pat) = convertHPatToGPat pat
convertHPatToGPat (H.PWildCard _) = G.UnderscorePat
convertHPatToGPat (H.PInfixApp _ patL op patR) =
  if isSpecialConstr op
    then G.ArgsPat (qNameToQId op) [convertHPatToGPat patL, convertHPatToGPat patR]
    else G.InfixPat (convertHPatToGPat patL) (qNameToText op) (convertHPatToGPat patR)
convertHPatToGPat (H.PTuple _ _ pats) = G.ArgsPat (strToQId "P") (convertHPatListToGPatList pats)
convertHPatToGPat (H.PList _ []) = G.ArgsPat (strToQId "Nil") []
convertHPatToGPat pat = error ("Haskell pattern not implemented: " ++ show pat)

needsArgumentsSentence :: Show l => H.DeclHead l -> [H.QualConDecl l] -> Bool
needsArgumentsSentence declHead qConDecls = not (null binders) && hasNonInferrableConstr qConDecls
  where
    binders = applyToDeclHeadTyVarBinds declHead convertTyVarBindToBinder

--check if function is recursive
isRecursive :: Show l => H.Name l -> H.Rhs l -> Bool
isRecursive name rhs = elem (getString name) (termToStrings (convertRhsToTerm rhs))

importPath :: String
importPath = "Add LoadPath \"../ImportedFiles\". \n \r"

predefinedDataTypes :: [(G.Name, [G.Qualid])]
predefinedDataTypes =
  [ (strToGName "bool", [strToQId "true", strToQId "false"])
  , (strToGName "List", [strToQId "Cons", strToQId "Nil"])
  , (strToGName "Pair", [strToQId "P"])
  ]

--print the converted module
printCoqAST :: G.Sentence -> IO ()
printCoqAST x = putStrLn (renderCoqAst (importDefinitions ++ [x]))

writeCoqFile :: String -> G.Sentence -> IO ()
writeCoqFile path x = writeFile path (renderCoqAst (importDefinitions ++ [x]))

renderCoqAst :: [G.Sentence] -> String
renderCoqAst sentences =
  importPath ++ concat [(TL.unpack . displayT . renderPretty 0.67 120 . renderGallina) s ++ "\n \r" | s <- sentences]
