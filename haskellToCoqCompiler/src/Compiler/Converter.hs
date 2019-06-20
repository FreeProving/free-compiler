module Compiler.Converter where

import qualified Language.Coq.Gallina as G
import Language.Coq.Pretty (renderGallina)
import qualified Language.Haskell.Exts.Syntax as H

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
  , changeSimilarType
  , collapseApp
  , containsRecursiveCall
  , eqQId
  , gNameToQId
  , getBinderName
  , getConstrNames
  , getConstrNamesFromDataDecls
  , getInferredBindersFromRetType
  , getNameFromDeclHead
  , getNamesFromDataDecls
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
  , qIdToStr
  , qNameToQId
  , qNameToStr
  , qNameToTerm
  , qNameToText
  , qNameToTypeTerm
  , qOpToQId
  , qOpToQOpId
  , strToGName
  , strToQId
  , strToTerm
  , termToQId
  , termToStrings
  , typeTerm
  )
import Compiler.MonadicConverter
  ( addBindOperatorsToDefinition
  , addReturnToRhs
  , getBindOperator
  , singletonTerm
  , toReturnTerm
  , transformBindersMonadic
  , transformTermMonadic
  )
import Compiler.NonEmptyList (singleton, toNonemptyList)
import Compiler.Types (ConversionMode(..), ConversionMonad(..))
import Compiler.Language.Coq.Pretty (printCoqAST, writeCoqFile)

import qualified GHC.Base as B

import Data.List (partition)
import Data.Maybe (fromJust, isJust)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

-- | Converts a Haskell module to a Gallina module sentence.
convertModule :: Show l => H.Module l -> ConversionMonad -> ConversionMode -> G.Sentence
convertModule (H.Module _ modHead _ _ decls) cMonad cMode =
  G.LocalModuleSentence
    (G.LocalModule
       (convertIdent $ maybe "unnamed" extractModuleName modHead)
       (dataSentences ++ convertModuleDecls rDecls (map filterForTypeSignatures typeSigs) dataTypes funs cMonad cMode))
  where
    (typeSigs, otherDecls) = partition isTypeSig decls
    (dataDecls, rDecls) = partition isDataDecl otherDecls
    dataSentences = convertModuleDecls dataDecls (map filterForTypeSignatures typeSigs) [] funs cMonad cMode
    dataTypes = predefinedDataTypes ++ zip (getNamesFromDataDecls dataDecls) (getConstrNamesFromDataDecls dataDecls)
    funs = getFunNames rDecls

-- | Converts a Haskell identifier to an identifier for the Coq AST.
convertIdent :: String -> G.Ident
convertIdent = T.pack

-- | Extracts the name of a Haskell module from its header.
extractModuleName :: Show l => H.ModuleHead l -> String
extractModuleName (H.ModuleHead _ (H.ModuleName _ modName) _ _) = modName

----------------------------------------------------------------------------------------------------------------------
getFunNames :: Show l => [H.Decl l] -> [G.Qualid]
getFunNames decls = map getQIdFromFunDecl (filter isFunction decls)

isFunction :: Show l => H.Decl l -> Bool
isFunction (H.FunBind _ _) = True
isFunction _ = False

getQIdFromFunDecl :: Show l => H.Decl l -> G.Qualid
getQIdFromFunDecl (H.FunBind _ (H.Match _ name _ _ _:_)) = nameToQId name

convertModuleDecls ::
     Show l
  => [H.Decl l]
  -> [G.TypeSignature]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  -> [G.Qualid]
  -> ConversionMonad
  -> ConversionMode
  -> [G.Sentence]
convertModuleDecls (H.FunBind _ (x:xs):ds) typeSigs dataTypes funs cMonad cMode =
  convertMatchDef x typeSigs dataTypes funs cMonad cMode ++ convertModuleDecls ds typeSigs dataTypes funs cMonad cMode
convertModuleDecls (H.DataDecl _ _ Nothing declHead qConDecl _:ds) typeSigs dataTypes funs cMonad cMode =
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
     Show l
  => H.Pat l
  -> H.Rhs l
  -> [G.TypeSignature]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  -> ConversionMonad
  -> G.Definition
convertPatBindToDefinition pat rhs typeSigs dataTypes cMonad = G.DefinitionDef G.Global name binders returnType rhsTerm
  where
    dataNames = map fst dataTypes
    binders = addInferredTypesToSignature [] (map fst dataTypes) (fromJust returnType)
    name = patToQID pat
    typeSig = getTypeSignatureByQId typeSigs name
    returnType = convertReturnType typeSig cMonad
    -- FIXME This line is propably responsible for the inconsistent compilation
    -- of functions and pattern bindings. The parameters `typeSigs`, `binders`
    -- and `dataTypes` of `addReturnToRhs` need to be properly initialized
    -- (see `convertMatchToDefinition`) instead of setting them to `[]`.
    -- Ideally the translatioon of functions and pattern bindings share a
    -- common code base.
    rhsTerm = addReturnToRhs (convertRhsToTerm rhs (map snd (concatMap snd dataTypes)) cMonad) [] [] [] cMonad

convertArgumentSentences :: Show l => H.DeclHead l -> [H.QualConDecl l] -> [G.Sentence]
convertArgumentSentences declHead qConDecls =
  [G.ArgumentsSentence (G.Arguments Nothing con (convertArgumentSpec declHead)) | con <- constrToDefine]
  where
    constrToDefine = getConstrNames qConDecls

convertArgumentSpec :: Show l => H.DeclHead l -> [G.ArgumentSpec]
convertArgumentSpec declHead = [G.ArgumentSpec G.ArgMaximal varName Nothing | varName <- varNames]
  where
    varNames = applyToDeclHeadTyVarBinds declHead convertTyVarBindToName

convertDataTypeDecl :: Show l => H.DeclHead l -> [H.QualConDecl l] -> ConversionMonad -> G.Inductive
convertDataTypeDecl dHead qConDecl cMonad = G.Inductive (singleton (G.IndBody typeName binders typeTerm constrDecls)) []
  where
    typeName = changeSimilarType (applyToDeclHead dHead nameToQId)
    binders = applyToDeclHeadTyVarBinds dHead convertTyVarBindToBinder
    constrDecls =
      convertQConDecls
        qConDecl
        (getReturnTypeFromDeclHead (applyToDeclHeadTyVarBinds dHead convertTyVarBindToArg) typeName)
        cMonad

convertMatchDef ::
     Show l
  => H.Match l
  -> [G.TypeSignature]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
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
    rhsTerm = convertRhsToTerm rhs (map snd (concatMap snd dataTypes)) cMonad
    funName = nameToQId name

convertMatchToDefinition ::
     Show l
  => H.Name l
  -> [H.Pat l]
  -> H.Rhs l
  -> [G.TypeSignature]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
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
    bindersWithInferredTypes =
      addInferredTypesToSignature monadicBinders (map fst dataTypes) (getReturnType (fromJust typeSig))
    bindersWithFuel = addFuelBinder bindersWithInferredTypes
    rhsTerm = convertRhsToTerm rhs (map snd (concatMap snd dataTypes)) cMonad
    monadicTerm =
      addBindOperatorsToDefinition
        monadicBinders
        (addReturnToRhs rhsTerm typeSigs monadicBinders dataTypes cMonad)
        cMonad
    fueledTerm = addFuelArgToRecursiveCalls rhsTerm fuelTerm funCalls
    fueledMonadicTerm =
      addBindOperatorsToDefinition
        monadicBinders
        (addReturnToRhs fueledTerm typeSigs monadicBinders dataTypes cMonad)
        cMonad

convertMatchToFueledFixpoint ::
     Show l
  => H.Name l
  -> [H.Pat l]
  -> H.Rhs l
  -> [G.TypeSignature]
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
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
    bindersWithInferredTypes = addInferredTypesToSignature monadicBinders (map fst dataTypes) (getReturnType typeSig)
    rhsTerm = convertRhsToTerm rhs (map snd (concatMap snd dataTypes)) cMonad
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
  -> [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  -> ConversionMonad
  -> [G.Sentence]
convertMatchWithHelperFunction name pats rhs typeSigs dataTypes cMonad =
  [ G.FixpointSentence (convertMatchToMainFunction name binders rhsTerm typeSigs dataTypes cMonad)
  , G.DefinitionSentence (convertMatchToHelperFunction name binders rhsTerm typeSigs dataTypes cMonad)
  ]
  where
    rhsTerm = convertRhsToTerm rhs (map snd (concatMap snd dataTypes)) cMonad
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
  if eqQId constrName (termToQId term)
    then (suffixName, [], Just (convertToArrowTerm types term cMonad))
    else (constrName, [], Just (convertToArrowTerm types term cMonad))
  where
    constrName = nameToQId name
    suffixName = strToQId ((qIdToStr constrName) ++ "_")
convertQConDecl (H.QualConDecl _ _ _ (H.RecDecl _ name fieldDecls)) term cMonad =
  if eqQId constrName (termToQId term)
    then (suffixName, [], Just (G.Record (convertFieldDeclsToRecList fieldDecls cMonad)))
    else (constrName, [], Just (G.Record (convertFieldDeclsToRecList fieldDecls cMonad)))
  where
    constrName = nameToQId name
    suffixName = strToQId ((qIdToStr constrName) ++ "_")

convertFieldDeclsToRecList :: Show l => [H.FieldDecl l] -> ConversionMonad -> [(G.Qualid, G.Term)]
convertFieldDeclsToRecList fDecls m = [convertFieldDeclToRec f m | f <- fDecls]

convertFieldDeclToRec :: Show l => H.FieldDecl l -> ConversionMonad -> (G.Qualid, G.Term)
convertFieldDeclToRec (H.FieldDecl _ name ty) m = (fieldName, fieldType)
  where
    fieldName = nameToQId (head name)
    fieldType = convertTypeToMonadicTerm m ty

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
convertTypeToTerm (H.TyFun _ t1 t2) = G.Arrow (convertTypeToTerm t1) (convertTypeToTerm t2)
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

convertRhsToTerm :: Show l => H.Rhs l -> [Maybe G.Qualid] -> ConversionMonad -> G.Term
convertRhsToTerm (H.UnGuardedRhs _ expr) constrs m = collapseApp (convertExprToTerm constrs m expr)
convertRhsToTerm (H.GuardedRhss _ _) _ _ = error "Guards not implemented"

convertExprToTerm :: Show l => [Maybe G.Qualid] -> ConversionMonad -> H.Exp l -> G.Term
convertExprToTerm _ _ (H.Var _ qName) = qNameToTerm qName
convertExprToTerm constrs _ (H.Con _ qName) =
  if any (== conStr) (map (qIdToStr . fromJust) (filter isJust constrs))
    then strToTerm (conStr ++ "_")
    else qNameToTerm qName
  where
    conStr = qNameToStr qName
convertExprToTerm constrs m (H.List _ (x:[])) =
  G.App singletonTerm (singleton ((G.PosArg . convertExprToTerm constrs m) x))
convertExprToTerm constrs m (H.Paren _ expr) = G.Parens (convertExprToTerm constrs m expr)
convertExprToTerm constrs m (H.App _ expr1 expr2) =
  G.App
    ((collapseApp . convertExprToTerm constrs m) expr1)
    (singleton (G.PosArg ((collapseApp . convertExprToTerm constrs m) expr2)))
convertExprToTerm constrs m (H.InfixApp _ exprL qOp exprR) =
  if isSpecialOperator qOp
    then G.App
           (G.Qualid (qOpToQId qOp))
           (toNonemptyList
              [ G.PosArg ((collapseApp . convertExprToTerm constrs m) exprL)
              , G.PosArg ((collapseApp . convertExprToTerm constrs m) exprR)
              ])
    else G.App
           (G.Qualid (qOpToQOpId qOp))
           (toNonemptyList
              [ G.PosArg ((collapseApp . convertExprToTerm constrs m) exprL)
              , G.PosArg ((collapseApp . convertExprToTerm constrs m) exprR)
              ])
convertExprToTerm constrs m (H.Case _ expr altList) =
  G.Match
    (singleton (G.MatchItem (convertExprToTerm constrs m expr) Nothing Nothing))
    Nothing
    (convertAltListToEquationList altList constrs m)
convertExprToTerm constrs m (H.If _ cond thenExpr elseExpr) =
  G.If
    G.SymmetricIf
    (convertExprToTerm constrs m cond)
    Nothing
    ((collapseApp . convertExprToTerm constrs m) thenExpr)
    ((collapseApp . convertExprToTerm constrs m) elseExpr)
convertExprToTerm constrs m (H.Lambda _ pats expr) =
  G.Fun
    (toNonemptyList binders)
    (G.App
       (getBindOperator m)
       (toNonemptyList
          [ G.PosArg (getBinderName (head binders))
          , G.PosArg (G.Fun (toNonemptyList suffixBinders) (toReturnTerm rhs m))
          ]))
  where
    rhs = convertExprToTerm constrs m expr
    binders = convertPatsToBinders pats Nothing
    suffixBinders = map ((G.Inferred G.Explicit) . strToGName . (++ "'") . qIdToStr . termToQId . getBinderName) binders
convertExprToTerm _ _ (H.Lit _ literal) = convertLiteralToTerm literal
convertExprToTerm constrs m (H.Tuple _ _ exprs) =
  G.App (G.Qualid (strToQId "P")) (toNonemptyList [(G.PosArg . convertExprToTerm constrs m) e | e <- exprs])
convertExprToTerm _ _ (H.List _ []) = G.Qualid (strToQId "Nil")
convertExprToTerm _ _ expr = error ("Haskell expression not implemented: " ++ show expr)

convertLiteralToTerm :: Show l => H.Literal l -> G.Term
convertLiteralToTerm (H.Char _ char _) = G.HsChar char
convertLiteralToTerm (H.String _ str _) = G.String (T.pack str)
convertLiteralToTerm (H.Int _ _ int) = G.Qualid (strToQId int)
convertLiteralToTerm literal = error ("Haskell Literal not implemented: " ++ show literal)

convertAltListToEquationList :: Show l => [H.Alt l] -> [Maybe G.Qualid] -> ConversionMonad -> [G.Equation]
convertAltListToEquationList altList constrs m = [convertAltToEquation s constrs m | s <- altList]

convertAltToEquation :: Show l => H.Alt l -> [Maybe G.Qualid] -> ConversionMonad -> G.Equation
convertAltToEquation (H.Alt _ pat rhs _) constrs m =
  G.Equation (singleton (G.MultPattern (singleton (convertHPatToGPat pat constrs)))) (convertRhsToTerm rhs constrs m)

convertHPatListToGPatList :: Show l => [H.Pat l] -> [Maybe G.Qualid] -> [G.Pattern]
convertHPatListToGPatList patList constrs = [convertHPatToGPat s constrs | s <- patList]

convertHPatToGPat :: Show l => H.Pat l -> [Maybe G.Qualid] -> G.Pattern
convertHPatToGPat (H.PVar _ name) constrs =
  if any (== varQid) (map fromJust (filter isJust constrs))
    then G.QualidPat (strToQId ((qIdToStr varQid) ++ "_"))
    else G.QualidPat varQid
  where
    varQid = nameToQId name
convertHPatToGPat (H.PApp _ qName pList) constrs =
  if any (== conQid) (map fromJust (filter isJust constrs))
    then G.ArgsPat conQid' (convertHPatListToGPatList pList constrs)
    else G.ArgsPat conQid (convertHPatListToGPatList pList constrs)
  where
    conQid = qNameToQId qName
    conQid' = strToQId (qNameToStr qName ++ "_")
convertHPatToGPat (H.PParen _ pat) constrs = convertHPatToGPat pat constrs
convertHPatToGPat (H.PWildCard _) _ = G.UnderscorePat
convertHPatToGPat (H.PInfixApp _ patL op patR) constrs =
  if isSpecialConstr op
    then G.ArgsPat (qNameToQId op) [convertHPatToGPat patL constrs, convertHPatToGPat patR constrs]
    else G.InfixPat (convertHPatToGPat patL constrs) (qNameToText op) (convertHPatToGPat patR constrs)
convertHPatToGPat (H.PTuple _ _ pats) constrs = G.ArgsPat (strToQId "P") (convertHPatListToGPatList pats constrs)
convertHPatToGPat (H.PList _ []) _ = G.ArgsPat (strToQId "Nil") []
convertHPatToGPat pat _ = error ("Haskell pattern not implemented: " ++ show pat)

needsArgumentsSentence :: Show l => H.DeclHead l -> [H.QualConDecl l] -> Bool
needsArgumentsSentence declHead qConDecls = not (null binders) && hasNonInferrableConstr qConDecls
  where
    binders = applyToDeclHeadTyVarBinds declHead convertTyVarBindToBinder

predefinedDataTypes :: [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
predefinedDataTypes =
  [ (strToGName "bool", [(strToQId "true", Nothing), (strToQId "false", Nothing)])
  , (strToGName "List", [(strToQId "Cons", Nothing), (strToQId "Nil", Nothing)])
  , (strToGName "Pair", [(strToQId "P", Nothing)])
  , (strToGName "unit", [(strToQId "tt", Nothing)])
  ]
