module Compiler.Converter where

import qualified Language.Coq.Gallina          as G
import qualified Language.Haskell.Exts.Syntax  as H

import           Compiler.DependencyAnalysis    ( DependencyComponent(..)
                                                , groupDeclarations
                                                )
import           Compiler.Language.Coq.Preamble ( importDefinitions )
import           Compiler.Language.Coq.TypeSignature
import           Compiler.HelperFunctionConverter
                                                ( convertMatchToHelperFunction
                                                , convertMatchToMainFunction
                                                )
import           Compiler.HelperFunctions       ( addInferredTypesToSignature
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
                                                , getNameFromDeclHead
                                                , getNamesFromDataDecls
                                                , getReturnType
                                                , getReturnTypeFromDeclHead
                                                , getTypeSignatureByName
                                                , getTypeSignatureByQId
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
                                                , typeTerm
                                                )
import           Compiler.MonadicConverter      ( addBindOperatorsToDefinition
                                                , addReturnToRhs
                                                , getBindOperator
                                                , singletonTerm
                                                , toReturnTerm
                                                , transformBindersMonadic
                                                , transformTermMonadic
                                                )
import           Compiler.NonEmptyList          ( singleton
                                                , toNonEmptyList
                                                )
import           Compiler.Types                 ( ConversionMonad(..) )

import           Data.List                      ( partition )
import           Data.Maybe                     ( fromJust
                                                , isJust
                                                )
import qualified Data.Text                     as T

-- | The @Environment@ data type encapsulates the state of the compiler
--   including the currently defined functions and types as well as the
--   configured conversion options.
data Environment = Environment
  { typeSignatures :: [TypeSignature]
  , dataTypes      :: [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
  , conversionMonad :: ConversionMonad
  }

-------------------------------------------------------------------------------
-- Utility functions                                                         --
-------------------------------------------------------------------------------

-- | Converts a Haskell identifier to an identifier for the Coq AST.
convertIdent :: String -> G.Ident
convertIdent = T.pack

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Converts a Haskell module to a Gallina module sentence and adds the
--   import definitions required by the generated Coq code.
convertModuleWithPreamble
  :: Show l => H.Module l -> ConversionMonad -> [G.Sentence]
convertModuleWithPreamble ast cMonad =
  importDefinitions cMonad ++ [convertModule ast cMonad]

-- | Converts a Haskell module to a Gallina module sentence.
--
--   If no module header is present the generated module is called @"unnamed"@.
convertModule :: Show l => H.Module l -> ConversionMonad -> G.Sentence
convertModule (H.Module _ modHead _ _ decls) cMonad = G.LocalModuleSentence
  (G.LocalModule modName sentences)
 where
  modName    = convertIdent (maybe "unnamed" extractModuleName modHead)

  components = groupDeclarations decls
  sentences  = concatMap convertComponent components

  -- TODO Add support for mutual recursion.
  -- TODO Actually use recursion information.
  convertComponent (NonRecursive decl  ) = convertDecl env decl
  convertComponent (Recursive    [decl]) = convertDecl env decl
  convertComponent (Recursive _) =
    error "mutually recursive declarations are not supported"

  -- TODO Build up environment during conversion.
  (typeSigs , nonTypeSigs) = partition isTypeSig decls
  (dataDecls, _          ) = partition isDataDecl nonTypeSigs
  env                      = Environment
    { typeSignatures  = convertTypeSignatures typeSigs
    , dataTypes       = predefinedDataTypes ++ zip
      (getNamesFromDataDecls dataDecls)
      (getConstrNamesFromDataDecls dataDecls)
    , conversionMonad = cMonad
    }

-- | Extracts the name of a Haskell module from its header.
extractModuleName :: Show l => H.ModuleHead l -> String
extractModuleName (H.ModuleHead _ (H.ModuleName _ modName) _ _) = modName

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | Converts all given type signatures.
convertTypeSignatures :: Show l => [H.Decl l] -> [TypeSignature]
convertTypeSignatures = concatMap convertTypeSignature

-- | Converts a Haskell type signature for one or more identifiers of the same
--   type to a list of Gallina type signatures (one for each identifier).
convertTypeSignature :: Show l => H.Decl l -> [TypeSignature]
convertTypeSignature (H.TypeSig _ names funType) = map
  (\name -> TypeSignature (nameToGName name) types)
  names
 where
  types :: [G.Term]
  types = convertTypeToTerms funType

-------------------------------------------------------------------------------
-- Declarations                                                              --
-------------------------------------------------------------------------------

-- | Converts all Haskell declarations in the given list to Coq.
--   The list must neither contain type signatures nor any unsuported
--   kind of declaration (e.g. type class declarations).
convertDecls :: Show l => Environment -> [H.Decl l] -> [G.Sentence]
convertDecls = concatMap . convertDecl

-- | Converts a Haskell declaration to Coq.
--
--   A list is returned because some declarations in Haskell correspond to
--   multiple Sentences in Coq (e.g. for a recursive function we generate
--   a helper function in addition to the main function).
--
--   Each kind of declaration is translate by a more concrete function
--   defined below.
convertDecl :: Show l => Environment -> H.Decl l -> [G.Sentence]
convertDecl env (H.FunBind _ [x]) = convertMatchDef env x
convertDecl env (H.DataDecl _ _ Nothing declHead qConDecl _) =
  G.InductiveSentence (convertDataTypeDecl env declHead qConDecl)
    : if needsArgumentsSentence declHead
        then convertArgumentSentences declHead qConDecl
        else []
convertDecl _ (H.TypeDecl _ declHead ty) =
  [G.DefinitionSentence (convertTypeDeclToDefinition declHead ty)]
convertDecl env (H.PatBind _ pat rhs _) =
  [G.DefinitionSentence (convertPatBindToDefinition env pat rhs)]
convertDecl _ decl =
  error ("Top-level declaration not implemented: " ++ show decl)

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Translates a single rule of a Haskell function declaration to a
--   function (or fixpoint) definition in Coq.
convertMatchDef :: Show l => Environment -> H.Match l -> [G.Sentence]
convertMatchDef env (H.Match _ name mPats rhs _) =
  if containsRecursiveCall rhsTerm funName
    then convertMatchWithHelperFunction env name mPats rhs
    else [G.DefinitionSentence (convertMatchToDefinition env name mPats rhs)]
 where
  rhsTerm = convertRhsToTerm rhs
                             (map snd (concatMap snd (dataTypes env)))
                             (conversionMonad env)
  funName = nameToQId name

-- | Converts a non-recursive Haskell function declaration to Coq.
convertMatchToDefinition
  :: Show l
  => Environment
  -> H.Name l  -- ^ The name of the Haskell function.
  -> [H.Pat l] -- ^ The argument patterns of the Haskell function.
  -> H.Rhs l   -- ^ The right hand side of the Haskell function.
  -> G.Definition
convertMatchToDefinition env name pats rhs = G.DefinitionDef
  G.Global
  funName
  bindersWithInferredTypes
  returnType
  monadicTerm
 where
  returnType               = convertReturnType typeSig (conversionMonad env)
  funName                  = nameToQId name
  typeSig                  = getTypeSignatureByName (typeSignatures env) name
  binders                  = convertPatsToBinders pats typeSig
  monadicBinders = transformBindersMonadic binders (conversionMonad env)
  bindersWithInferredTypes = addInferredTypesToSignature
    monadicBinders
    (map fst (dataTypes env))
    (getReturnType (fromJust typeSig))
  rhsTerm = convertRhsToTerm rhs
                             (map snd (concatMap snd (dataTypes env)))
                             (conversionMonad env)
  monadicTerm = addBindOperatorsToDefinition
    monadicBinders
    (addReturnToRhs rhsTerm
                    (typeSignatures env)
                    monadicBinders
                    (dataTypes env)
                    (conversionMonad env)
    )
    (conversionMonad env)

-- | Converts a recursive Haskell function declaration to Coq.
--
--   The recursive function is splitted into a recursive helper function and a
--   non-recursive main function.
convertMatchWithHelperFunction
  :: Show l
  => Environment
  -> H.Name l  -- ^ The name of the Haskell function.
  -> [H.Pat l] -- ^ The argument patterns of the Haskell function.
  -> H.Rhs l   -- ^ The right hand side of the Haskell function.
  -> [G.Sentence]
convertMatchWithHelperFunction env name pats rhs =
  [ G.FixpointSentence
    (convertMatchToMainFunction name
                                binders
                                rhsTerm
                                (typeSignatures env)
                                (dataTypes env)
                                (conversionMonad env)
    )
  , G.DefinitionSentence
    (convertMatchToHelperFunction name
                                  binders
                                  rhsTerm
                                  (typeSignatures env)
                                  (dataTypes env)
                                  (conversionMonad env)
    )
  ]
 where
  rhsTerm = convertRhsToTerm rhs
                             (map snd (concatMap snd (dataTypes env)))
                             (conversionMonad env)
  binders = convertPatsToBinders pats typeSig
  typeSig = getTypeSignatureByName (typeSignatures env) name

-- | Extracts the return type from the type signature of a function.
--
--   TODO Because we require the type signatures to be provided for all
--        defined functions, the first argument can never be @Nothing@.
convertReturnType :: Maybe TypeSignature -> ConversionMonad -> Maybe G.Term
convertReturnType Nothing _ = Nothing
-- FIXME In general (last types) is not the return type of the function.
convertReturnType (Just (TypeSignature _ types)) cMonad =
  Just (transformTermMonadic (last types) cMonad)

-- | Converts the right hand side of a Haskell function to Coq.
convertRhsToTerm
  :: Show l
  => H.Rhs l          -- ^ The right hand side of the function.
  -> [Maybe G.Qualid] -- ^ The original names of constructors with @_@ suffix
                      --   in Coq or @Nothing@ for constructors that were not
                      --   renamed.
  -> ConversionMonad
  -> G.Term
convertRhsToTerm (H.UnGuardedRhs _ expr) constrs m =
  collapseApp (convertExprToTerm constrs m expr)
convertRhsToTerm (H.GuardedRhss _ _) _ _ = error "Guards not implemented"

-------------------------------------------------------------------------------
-- Pattern bindings                                                          --
-------------------------------------------------------------------------------

-- | Converts a Haskell pattern binding to Coq.
--
--   The pattern must be a variable pattern. Therefore every pattern binding
--   corresponds to a function with zero arguments.
convertPatBindToDefinition
  :: Show l => Environment -> H.Pat l -> H.Rhs l -> G.Definition
convertPatBindToDefinition env pat rhs = G.DefinitionDef G.Global
                                                         name
                                                         binders
                                                         returnType
                                                         rhsTerm
 where
  binders = addInferredTypesToSignature []
                                        (map fst (dataTypes env))
                                        (fromJust returnType)
  name       = patToQID pat
  typeSig    = getTypeSignatureByQId (typeSignatures env) name
  returnType = convertReturnType typeSig (conversionMonad env)
  -- FIXME This line is propably responsible for the inconsistent compilation
  -- of functions and pattern bindings. The parameters `typeSigs`, `binders`
  -- and `dataTypes` of `addReturnToRhs` need to be properly initialized
  -- (see `convertMatchToDefinition`) instead of setting them to `[]`.
  -- Ideally the translatioon of functions and pattern bindings share a
  -- common code base.
  rhsTerm    = addReturnToRhs
    (convertRhsToTerm rhs
                      (map snd (concatMap snd (dataTypes env)))
                      (conversionMonad env)
    )
    []
    []
    []
    (conversionMonad env)

-------------------------------------------------------------------------------
-- Type synonym declarations                                                 --
-------------------------------------------------------------------------------

-- | Converts a Haskell type synonym declaration to Coq.
convertTypeDeclToDefinition
  :: Show l => H.DeclHead l -> H.Type l -> G.Definition
convertTypeDeclToDefinition dHead ty = G.DefinitionDef G.Global
                                                       name
                                                       binders
                                                       Nothing
                                                       rhs
 where
  name    = (gNameToQId . getNameFromDeclHead) dHead
  binders = applyToDeclHeadTyVarBinds dHead convertTyVarBindToBinder
  rhs     = convertTypeToTerm ty

-------------------------------------------------------------------------------
-- Data type declarations                                                    --
-------------------------------------------------------------------------------

-- | Converts a Haskell data type declaration to Coq.
convertDataTypeDecl
  :: Show l => Environment -> H.DeclHead l -> [H.QualConDecl l] -> G.Inductive
convertDataTypeDecl env dHead qConDecl = G.Inductive
  (singleton (G.IndBody typeName binders typeTerm constrDecls))
  []
 where
  typeName    = changeSimilarType (applyToDeclHead dHead nameToQId)
  binders     = applyToDeclHeadTyVarBinds dHead convertTyVarBindToBinder
  constrDecls = convertQConDecls
    qConDecl
    (getReturnTypeFromDeclHead
      (applyToDeclHeadTyVarBinds dHead convertTyVarBindToArg)
      typeName
    )
    (conversionMonad env)

-------------------------------------------------------------------------------
-- Constructor declarations                                                  --
-------------------------------------------------------------------------------

-- | Converts all constructor declarations of a data type from Haskell to Coq.
convertQConDecls
  :: Show l
  => [H.QualConDecl l] -- ^ All constructors of the data type.
  -> G.Term            -- ^ The Coq type produced by this constructor.
  -> ConversionMonad
  -> [(G.Qualid, [G.Binder], Maybe G.Term)]
convertQConDecls qConDecl term cMonad =
  [ convertQConDecl c term cMonad | c <- qConDecl ]

-- | Converts a single Haskell constructor declaration to Coq.
--
--   Supports only regular constructors, i.e. no infix or record constructors.
--
--   In the Coq AST constructors are represented by a tripple. The first
--   entry is the name of the constructor, the second entry is a list of named
--   arguments of the constructor and the final entry is the type returned
--   by the constructor.
convertQConDecl
  :: Show l
  => H.QualConDecl l -- ^ The constructor to convert.
  -> G.Term          -- ^ The Coq type produced by this constructor.
  -> ConversionMonad
  -> (G.Qualid, [G.Binder], Maybe G.Term)
convertQConDecl (H.QualConDecl _ Nothing Nothing (H.ConDecl _ name types)) term cMonad
  = if eqQId constrName (termToQId term)
    then (suffixName, [], Just (convertToArrowTerm types term cMonad))
    else (constrName, [], Just (convertToArrowTerm types term cMonad))
 where
  constrName = nameToQId name
  suffixName = strToQId ((qIdToStr constrName) ++ "_")

-- | Generates the type of a constructor in Coq from the arguments types
--   of the constructor in Haskell.
convertToArrowTerm
  :: Show l
  => [H.Type l] -- ^ The Haskell types of the constructor arguments.
  -> G.Term     -- ^ The Coq type produced by the constructor.
  -> ConversionMonad
  -> G.Term
convertToArrowTerm types returnType cMonad =
  buildArrowTerm (map (convertTypeToMonadicTerm cMonad) types) returnType

-- | Builds the type of a Coq function.
buildArrowTerm
  :: [G.Term]  -- ^ The Coq types of the arguments.
  -> G.Term -- ^ The return type of the Coq function.
  -> G.Term
buildArrowTerm terms returnType = foldr G.Arrow returnType terms

-------------------------------------------------------------------------------
-- Argument senetences for constructor declarations                          --
-------------------------------------------------------------------------------

-- | Tests whether @Arguments@ sentences need to be generated for the
--   constructors of a Haskell data type declaration.
--
--   The @Arguments@ sentences are needed if the data type is polymorphic.
needsArgumentsSentence
  :: Show l
  => H.DeclHead l      -- ^ The head of the data type declaration.
  -> Bool
needsArgumentsSentence declHead = not (null binders)
  where
    -- TODO A function to get the `TyVarBinds` would be better suited.
        binders = applyToDeclHeadTyVarBinds declHead convertTyVarBindToBinder

-- | Generates one @Arguments@ sentences for each constructor of a Haskell
--   data type declaration.
convertArgumentSentences
  :: Show l
  => H.DeclHead l      -- ^ The head of the data type declaration.
  -> [H.QualConDecl l] -- ^ The constructors of the data type.
  -> [G.Sentence]
convertArgumentSentences declHead qConDecls =
  [ G.ArgumentsSentence (G.Arguments Nothing con specs)
  | con <- constrToDefine
  ]
 where
  constrToDefine = getConstrNames qConDecls
  specs          = convertArgumentSpec declHead

-- | Generates one @G.ArgumentSpec@ for every type argument of a
--   data type declaration that marks the type argument as implicit.
convertArgumentSpec :: Show l => H.DeclHead l -> [G.ArgumentSpec]
convertArgumentSpec declHead =
  [ G.ArgumentSpec G.ArgMaximal varName Nothing | varName <- varNames ]
  where varNames = applyToDeclHeadTyVarBinds declHead convertTyVarBindToName

-------------------------------------------------------------------------------
-- Type variable bindings in data type declarations                          --
-------------------------------------------------------------------------------

-- | Gets the name of a Haskell type variable from the binding of the variable.
convertTyVarBindToName :: Show l => H.TyVarBind l -> G.Name
convertTyVarBindToName (H.KindedVar _ name _) = nameToGName name
convertTyVarBindToName (H.UnkindedVar _ name) = nameToGName name

-- | Converts the binding of a Haskell type variable to a positional argument
--   that can be used in Coq within the data type declaration to instantiate
--   the data type that is declared.
convertTyVarBindToArg :: Show l => H.TyVarBind l -> G.Arg
convertTyVarBindToArg (H.KindedVar _ _ _) =
  error "Kind-annotation not implemented"
convertTyVarBindToArg (H.UnkindedVar _ name) = G.PosArg (nameToTerm name)

-- | Converts the binding of a Haskell type variable to a binder that can
--   be used in Coq to declare an explicit type argument of an inductive
--   data type.
convertTyVarBindToBinder :: Show l => H.TyVarBind l -> G.Binder
convertTyVarBindToBinder (H.KindedVar _ _ _) =
  error "Kind-annotation not implemented"
convertTyVarBindToBinder (H.UnkindedVar _ name) =
  G.Typed G.Ungeneralizable G.Explicit (singleton (nameToGName name)) typeTerm

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Converts a Haskell expression to Coq.
convertExprToTerm
  :: Show l
  => [Maybe G.Qualid] -- ^ The original names of constructors with @_@ suffix
                      --   in Coq or @Nothing@ for constructors that were not
                      --   renamed.
  -> ConversionMonad
  -> H.Exp l          -- ^ The expression to convert.
  -> G.Term
convertExprToTerm _ _ (H.Var _ qName) = qNameToTerm qName
convertExprToTerm constrs _ (H.Con _ qName) =
  if any (== conStr) (map (qIdToStr . fromJust) (filter isJust constrs))
    then strToTerm (conStr ++ "_")
    else qNameToTerm qName
  where conStr = qNameToStr qName
-- TODO translate lists with more than one element.
convertExprToTerm constrs m (H.List _ (x : [])) =
  G.App singletonTerm (singleton ((G.PosArg . convertExprToTerm constrs m) x))
convertExprToTerm constrs m (H.Paren _ expr) =
  G.Parens (convertExprToTerm constrs m expr)
convertExprToTerm constrs m (H.App _ expr1 expr2) = G.App
  ((collapseApp . convertExprToTerm constrs m) expr1)
  (singleton (G.PosArg ((collapseApp . convertExprToTerm constrs m) expr2)))
convertExprToTerm constrs m (H.InfixApp _ exprL qOp exprR) =
  if isSpecialOperator qOp
    then G.App
      (G.Qualid (qOpToQId qOp))
      (toNonEmptyList
        [ G.PosArg ((collapseApp . convertExprToTerm constrs m) exprL)
        , G.PosArg ((collapseApp . convertExprToTerm constrs m) exprR)
        ]
      )
    else G.App
      (G.Qualid (qOpToQOpId qOp))
      (toNonEmptyList
        [ G.PosArg ((collapseApp . convertExprToTerm constrs m) exprL)
        , G.PosArg ((collapseApp . convertExprToTerm constrs m) exprR)
        ]
      )
convertExprToTerm constrs m (H.Case _ expr altList) = G.Match
  (singleton (G.MatchItem (convertExprToTerm constrs m expr) Nothing Nothing))
  Nothing
  (convertAltListToEquationList altList constrs m)
convertExprToTerm constrs m (H.If _ cond thenExpr elseExpr) = G.If
  G.SymmetricIf
  (convertExprToTerm constrs m cond)
  Nothing
  ((collapseApp . convertExprToTerm constrs m) thenExpr)
  ((collapseApp . convertExprToTerm constrs m) elseExpr)
convertExprToTerm constrs m (H.Lambda _ pats expr) = G.Fun
  (toNonEmptyList binders)
  (G.App
    (getBindOperator m)
    (toNonEmptyList
      [ G.PosArg (getBinderName (head binders))
      , G.PosArg (G.Fun (toNonEmptyList suffixBinders) (toReturnTerm rhs m))
      ]
    )
  )
 where
  rhs           = convertExprToTerm constrs m expr
  binders       = convertPatsToBinders pats Nothing
  suffixBinders = map
    ( (G.Inferred G.Explicit)
    . strToGName
    . (++ "'")
    . qIdToStr
    . termToQId
    . getBinderName
    )
    binders
convertExprToTerm _       _ (H.Lit _ literal  ) = convertLiteralToTerm literal
convertExprToTerm constrs m (H.Tuple _ _ exprs) = G.App
  (G.Qualid (strToQId "P"))
  (toNonEmptyList [ (G.PosArg . convertExprToTerm constrs m) e | e <- exprs ])
convertExprToTerm _ _ (H.List _ []) = G.Qualid (strToQId "Nil")
convertExprToTerm _ _ expr =
  error ("Haskell expression not implemented: " ++ show expr)

-- | Converts a Haskell literal to Coq.
--
--   TODO Officially we don't support any literal but `Int` literals.
--        Thus the conversion of `String` and `Char` literals could be
--        removed.
convertLiteralToTerm :: Show l => H.Literal l -> G.Term
convertLiteralToTerm (H.Char   _ char _  ) = G.HsChar char
convertLiteralToTerm (H.String _ str  _  ) = G.String (T.pack str)
convertLiteralToTerm (H.Int    _ _    int) = G.Qualid (strToQId int)
convertLiteralToTerm literal =
  error ("Haskell Literal not implemented: " ++ show literal)

-------------------------------------------------------------------------------
-- Case expressions                                                          --
-------------------------------------------------------------------------------

-- | Converts all alternatives of a Haskell @case@ expression to
--   equations of a Coq @match@ expression.
convertAltListToEquationList
  :: Show l
  => [H.Alt l]        -- ^ The alternatives.
  -> [Maybe G.Qualid] -- ^ The original names of constructors with @_@ suffix
                      --   in Coq or @Nothing@ for constructors that were not
                      --   renamed.
  -> ConversionMonad
  -> [G.Equation]
convertAltListToEquationList altList constrs m =
  [ convertAltToEquation s constrs m | s <- altList ]

-- | Converts an alternative of a Haskell @case@ expression to an equation
--   of a Coq @match@ expression.
convertAltToEquation
  :: Show l
  => H.Alt l          -- ^ The alternative.
  -> [Maybe G.Qualid] -- ^ The original names of constructors with @_@ suffix
                      --   in Coq or @Nothing@ for constructors that were not
                      --   renamed.
  -> ConversionMonad
  -> G.Equation
convertAltToEquation (H.Alt _ pat rhs _) constrs m = G.Equation
  (singleton (G.MultPattern (singleton (convertHPatToGPat pat constrs))))
  (convertRhsToTerm rhs constrs m)

-------------------------------------------------------------------------------
-- Patterns in case expressions                                              --
-------------------------------------------------------------------------------

-- | Converts a list of Haskell patterns to Coq patterns.
convertHPatListToGPatList
  :: Show l
  => [H.Pat l]        -- ^ The patterns.
  -> [Maybe G.Qualid] -- ^ The original names of constructors with @_@ suffix
                      --   in Coq or @Nothing@ for constructors that were not
                      --   renamed.
  -> [G.Pattern]
convertHPatListToGPatList patList constrs =
  [ convertHPatToGPat s constrs | s <- patList ]

-- | Converts a Haskell pattern to a Coq pattern.
convertHPatToGPat
  :: Show l
  => H.Pat l          -- ^ The pattern.
  -> [Maybe G.Qualid] -- ^ The original names of constructors with @_@ suffix
                      --   in Coq or @Nothing@ for constructors that were not
                      --   renamed.
  -> G.Pattern
convertHPatToGPat (H.PVar _ name) constrs =
  if any (== varQid) (map fromJust (filter isJust constrs))
    then G.QualidPat (strToQId ((qIdToStr varQid) ++ "_"))
    else G.QualidPat varQid
  where varQid = nameToQId name
convertHPatToGPat (H.PApp _ qName pList) constrs =
  if any (== conQid) (map fromJust (filter isJust constrs))
    then G.ArgsPat conQid' (convertHPatListToGPatList pList constrs)
    else G.ArgsPat conQid (convertHPatListToGPatList pList constrs)
 where
  conQid  = qNameToQId qName
  conQid' = strToQId (qNameToStr qName ++ "_")
convertHPatToGPat (H.PParen _ pat) constrs = convertHPatToGPat pat constrs
convertHPatToGPat (H.PWildCard _) _ = G.UnderscorePat
convertHPatToGPat (H.PInfixApp _ patL op patR) constrs = if isSpecialConstr op
  then G.ArgsPat
    (qNameToQId op)
    [convertHPatToGPat patL constrs, convertHPatToGPat patR constrs]
  else G.InfixPat (convertHPatToGPat patL constrs)
                  (qNameToText op)
                  (convertHPatToGPat patR constrs)
convertHPatToGPat (H.PTuple _ _ pats) constrs =
  G.ArgsPat (strToQId "P") (convertHPatListToGPatList pats constrs)
convertHPatToGPat (H.PList _ []) _ = G.ArgsPat (strToQId "Nil") []
convertHPatToGPat pat _ =
  error ("Haskell pattern not implemented: " ++ show pat)

-------------------------------------------------------------------------------
-- Patterns in function declarations                                         --
-------------------------------------------------------------------------------

-- | Converts variable patterns (function parameters) to Coq binders
--   of the variables.
--
--  TODO Because we require the type signatures to be present for
--       all defined functions, the second parameter cannot be @Nothing@.
convertPatsToBinders
  :: Show l => [H.Pat l] -> Maybe TypeSignature -> [G.Binder]
convertPatsToBinders patList Nothing = [ convertPatToBinder p | p <- patList ]
convertPatsToBinders patList (Just (TypeSignature _ typeList)) =
  -- FIXME @init typeList@ is not necessarily the list of argument types.
  convertPatsAndTypeSigsToBinders patList (init typeList)

-- | Converts a variable pattern (function parameter) for which no type
--   information is available to a Coq binder.
--
--   The type of the generated binder is inferred.
convertPatToBinder :: Show l => H.Pat l -> G.Binder
convertPatToBinder (H.PVar _ name) = G.Inferred G.Explicit (nameToGName name)
convertPatToBinder pat = error ("Pattern not implemented: " ++ show pat)

-- | Converts variable patterns (function parameters) to Coq binders
--   of the variables to the corresponding types.
convertPatsAndTypeSigsToBinders :: Show l => [H.Pat l] -> [G.Term] -> [G.Binder]
convertPatsAndTypeSigsToBinders = zipWith convertPatAndTypeSigToBinder

-- | Converts a variable pattern (function parameter) to a Coq binder
--   of the variable to the given Coq type.
convertPatAndTypeSigToBinder
  :: Show l
  => H.Pat l -- ^ A variable pattern.
  -> G.Term  -- ^ The Coq type pf the parameter.
  -> G.Binder
convertPatAndTypeSigToBinder (H.PVar _ name) term =
  G.Typed G.Ungeneralizable G.Explicit (singleton (nameToGName name)) term
convertPatAndTypeSigToBinder pat _ =
  error ("Haskell pattern not implemented: " ++ show pat)

-------------------------------------------------------------------------------
-- Type expressions                                                          --
-------------------------------------------------------------------------------

-- | Splits a function type into the argument and return types.
convertTypeToTerms :: Show l => H.Type l -> [G.Term]
convertTypeToTerms (H.TyFun _ type1 type2) =
  convertTypeToTerm type1 : convertTypeToTerms type2
convertTypeToTerms t = [convertTypeToTerm t]

-- | Converts a Haskell type to Coq without monadic transformation.
convertTypeToTerm :: Show l => H.Type l -> G.Term
convertTypeToTerm (H.TyVar   _ name ) = nameToTypeTerm name
convertTypeToTerm (H.TyCon   _ qName) = qNameToTypeTerm qName
convertTypeToTerm (H.TyParen _ ty   ) = G.Parens (convertTypeToTerm ty)
convertTypeToTerm (H.TyApp _ type1 type2) =
  G.App (convertTypeToTerm type1) (singleton (convertTypeToArg type2))
convertTypeToTerm (H.TyList _ ty) =
  G.App listTerm (singleton (G.PosArg (convertTypeToTerm ty)))
convertTypeToTerm (H.TyTuple _ _ tys) =
  G.App pairTerm (toNonEmptyList [ convertTypeToArg t | t <- tys ])
convertTypeToTerm (H.TyFun _ t1 t2) =
  G.Arrow (convertTypeToTerm t1) (convertTypeToTerm t2)
convertTypeToTerm ty = error ("Haskell-type not implemented: " ++ show ty)

-- | Converts a Haskell type such that it can be used as an argument to a
--   type constructor application.
convertTypeToArg :: Show l => H.Type l -> G.Arg
convertTypeToArg ty = G.PosArg (convertTypeToTerm ty)

-- | Converts a Haskell type to Coq (see @convertTypeToTerm@) and wraps
--   the result with the type constructor of the monad.
--   Function types are wrapped recursively.
convertTypeToMonadicTerm :: Show l => ConversionMonad -> H.Type l -> G.Term
convertTypeToMonadicTerm cMonad (H.TyVar _ name) =
  transformTermMonadic (nameToTypeTerm name) cMonad
convertTypeToMonadicTerm cMonad (H.TyCon _ qName) =
  transformTermMonadic (qNameToTypeTerm qName) cMonad
convertTypeToMonadicTerm cMonad (H.TyParen _ ty) =
  transformTermMonadic (G.Parens (convertTypeToTerm ty)) cMonad
convertTypeToMonadicTerm _ ty = convertTypeToTerm ty

-------------------------------------------------------------------------------
-- Functions that don't belong here                                          --
-------------------------------------------------------------------------------

-- | Names of predefined data types and their constructors.
--
--   The second element of the entries for the constructors (of type
--   @Maybe G.Qualid@) is the original name of the constructor if an
--   underscore was appended or @Nothing@ if the constructor name is
--   unchanged.
predefinedDataTypes :: [(G.Name, [(G.Qualid, Maybe G.Qualid)])]
predefinedDataTypes =
  [ ( strToGName "bool"
    , [(strToQId "true", Nothing), (strToQId "false", Nothing)]
    )
  , (strToGName "List", [(strToQId "Cons", Nothing), (strToQId "Nil", Nothing)])
  , (strToGName "Pair", [(strToQId "P", Nothing)])
  , (strToGName "unit", [(strToQId "tt", Nothing)])
  ]
