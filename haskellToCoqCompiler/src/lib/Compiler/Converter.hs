-- | This module contains the new implementation of the converter from
--   Haskell to Coq using the @Free@ monad.

module Compiler.Converter
  ( defaultEnvironment
    -- * Modules
  , convertModule
  , convertModuleWithPreamble
  , convertDecls
    -- * Data type declarations
  , convertTypeComponent
  , convertDataDecls
  , convertDataDecl
    -- * Function declarations
  , convertFuncComponent
  , convertNonRecFuncDecl
  , convertRecFuncDecls
    -- * Type expressions
  , convertType
  , convertType'
   -- * Expressions
  , convertExpr
  )
where

import           Control.Monad                  ( mapAndUnzipM
                                                , zipWithM
                                                )
import           Control.Monad.Extra            ( concatMapM )
import           Data.Composition
import           Data.Maybe                     ( maybe
                                                , catMaybes
                                                )
import           Data.List                      ( elemIndex )
import           Data.List.NonEmpty             ( NonEmpty((:|)) )
import qualified Data.List.NonEmpty            as NonEmpty

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyGraph
import           Compiler.Analysis.DependencyExtraction
import           Compiler.Analysis.PartialityAnalysis
import           Compiler.Converter.Fresh
import           Compiler.Converter.Inliner
import           Compiler.Converter.State
import           Compiler.Converter.Renamer
import qualified Compiler.Language.Coq.AST     as G
import qualified Compiler.Language.Coq.Base    as CoqBase
import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.Pretty
import           Compiler.Reporter
import           Compiler.SrcSpan

-- | Initially the environment contains the predefined functions, data types
--   and their constructors from the Coq Base library that accompanies this
--   compiler.
defaultEnvironment :: Environment
defaultEnvironment = CoqBase.predefine emptyEnvironment

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Converts a Haskell module to a Gallina module sentence and adds
--   import sentences for the Coq Base library that accompanies the compiler.
convertModuleWithPreamble :: HS.Module -> Converter [G.Sentence]
convertModuleWithPreamble ast = do
  coqAst <- convertModule ast
  return [CoqBase.imports, coqAst]

-- | Converts a Haskell module to a Gallina module sentence.
--
--   If no module header is present the generated module is called @"Main"@.
convertModule :: HS.Module -> Converter G.Sentence
convertModule (HS.Module _ maybeIdent decls) = do
  let modName = G.ident (maybe "Main" id maybeIdent)
  decls' <- convertDecls decls
  return (G.LocalModuleSentence (G.LocalModule modName decls'))

-- | Converts the declarations from a Haskell module to Coq.
convertDecls :: [HS.Decl] -> Converter [G.Sentence]
convertDecls decls = do
  typeDecls' <- concatMapM convertTypeComponent (groupDependencies typeGraph)
  mapM_ (modifyEnv . definePartial) (partialFunctions funcGraph)
  mapM_ filterAndDefineTypeSig      decls
  funcDecls' <- concatMapM convertFuncComponent (groupDependencies funcGraph)
  return (typeDecls' ++ funcDecls')
 where
  typeGraph, funcGraph :: DependencyGraph
  typeGraph = typeDependencyGraph decls
  funcGraph = funcDependencyGraph decls

-------------------------------------------------------------------------------
-- Data type declarations                                                    --
-------------------------------------------------------------------------------

-- | Converts a strongly connected component of the type dependency graph.
convertTypeComponent :: DependencyComponent -> Converter [G.Sentence]
convertTypeComponent (NonRecursive decl) =
  -- TODO handle type declaration diffently.
  convertDataDecls [decl]
convertTypeComponent (Recursive decls) =
  -- TODO filter type declarations, handle them separatly and expand
  --      type synonyms from this component in data declarations.
  convertDataDecls decls

-- | Converts multiple (mutually recursive) Haskell data type declaration
--   declarations.
--
--   Before the declarations are actually translated, their identifiers are
--   inserted into the current environement. Otherwise the data types would
--   not be able to depend on each other. The identifiers for the constructors
--   are inserted into the current environmen as well. This makes the
--   constructors more likely to keep their original name if there is a type
--   variable with the same (lowercase) name.
--
--   After the @Inductive@ sentences for the data type declarations there
--   is one @Arguments@ sentence and one smart constructor declaration for
--   each constructor declaration of the given data types.
convertDataDecls :: [HS.Decl] -> Converter [G.Sentence]
convertDataDecls dataDecls = do
  mapM_ defineDataDecl dataDecls
  (indBodies, extraSentences) <- mapAndUnzipM convertDataDecl dataDecls
  return
    ( -- TODO comment
      G.InductiveSentence (G.Inductive (NonEmpty.fromList indBodies) [])
    : concat extraSentences
    )

-- | Converts a Haskell data type declaration to the body of a Coq @Inductive@
--   sentence, the @Arguments@ sentences for it's constructors and the smart
--   constructor declarations.
--
--   This function assumes, that the identifiers for the declared data type
--   and it's (smart) constructors are defined already (see 'defineDataDecl').
--   Type variables declared by the data type or the smart constructors are
--   not visible outside of this function.
convertDataDecl :: HS.Decl -> Converter (G.IndBody, [G.Sentence])
convertDataDecl (HS.DataDecl srcSpan (HS.DeclIdent _ ident) typeVarDecls conDecls)
  = do
    (body, argumentsSentences) <- generateBodyAndArguments
    smartConDecls              <- mapM generateSmartConDecl conDecls
    return
      ( body
      , G.comment ("Arguments sentences for " ++ ident)
      :  argumentsSentences
      ++ G.comment ("Smart constructors for " ++ ident)
      :  smartConDecls
      )
 where
  -- | The Haskell type produced by the constructors of the data type.
  returnType :: HS.Type
  returnType = HS.typeApp
    srcSpan
    (HS.Ident ident)
    (map (HS.TypeVar srcSpan . HS.fromDeclIdent) typeVarDecls)

  -- | Generates the body of the @Inductive@ sentence and the @Arguments@
  --   sentences for the constructors but not the smart the smart constructors
  --   of the data type.
  --
  --   Type variables declared by the data type declaration are visible to the
  --   constructor declarations and @Arguments@ sentences created by this
  --   function, but not outside this function. This allows the smart
  --   constructors to reuse the identifiers for their type arguments (see
  --   'generateSmartConDecl').
  generateBodyAndArguments :: Converter (G.IndBody, [G.Sentence])
  generateBodyAndArguments = localEnv $ do
    Just qualid        <- inEnv $ lookupIdent TypeScope (HS.Ident ident)
    typeVarDecls'      <- convertTypeVarDecls G.Explicit typeVarDecls
    conDecls'          <- mapM convertConDecl conDecls
    argumentsSentences <- mapM generateArgumentsSentence conDecls
    return
      ( G.IndBody qualid
                  (genericArgDecls G.Explicit ++ typeVarDecls')
                  G.sortType
                  conDecls'
      , argumentsSentences
      )

  -- | Converts a constructor of the data type.
  convertConDecl :: HS.ConDecl -> Converter (G.Qualid, [G.Binder], Maybe G.Term)
  convertConDecl (HS.ConDecl _ (HS.DeclIdent _ conIdent) args) = do
    Just conQualid <- inEnv $ lookupIdent ConScope (HS.Ident conIdent)
    args'          <- mapM convertType args
    returnType'    <- convertType' returnType
    return (conQualid, [], Just (args' `G.arrows` returnType'))

  -- | Generates the @Arguments@ sentence for the given constructor declaration.
  generateArgumentsSentence :: HS.ConDecl -> Converter G.Sentence
  generateArgumentsSentence (HS.ConDecl _ (HS.DeclIdent _ conIdent) _) = do
    Just qualid <- inEnv $ lookupIdent ConScope (HS.Ident conIdent)
    let typeVarIdents = map (HS.Ident . HS.fromDeclIdent) typeVarDecls
    typeVarQualids <- mapM (inEnv . lookupIdent TypeScope) typeVarIdents
    return
      (G.ArgumentsSentence
        (G.Arguments
          Nothing
          qualid
          [ G.ArgumentSpec G.ArgMaximal (G.Ident typeVarQualid) Nothing
          | typeVarQualid <- map fst CoqBase.freeArgs
            ++ catMaybes typeVarQualids
          ]
        )
      )

  -- | Generates the smart constructor declaration for the given constructor
  --   declaration.
  generateSmartConDecl :: HS.ConDecl -> Converter G.Sentence
  generateSmartConDecl (HS.ConDecl _ declIdent argTypes) = localEnv $ do
    let conIdent = HS.Ident (HS.fromDeclIdent declIdent)
    Just qualid             <- inEnv $ lookupIdent ConScope conIdent
    Just smartQualid        <- inEnv $ lookupIdent SmartConScope conIdent
    typeVarDecls'           <- convertTypeVarDecls G.Implicit typeVarDecls
    (argIdents', argDecls') <- mapAndUnzipM convertAnonymousArg
                                            (map Just argTypes)
    returnType' <- convertType returnType
    return
      (G.definitionSentence
        smartQualid
        (genericArgDecls G.Explicit ++ typeVarDecls' ++ argDecls')
        returnType'
        (generatePure
          (G.app (G.Qualid qualid) (map (G.Qualid . G.bare) argIdents'))
        )
      )

-- | Inserts the given data type declaration and its constructor declarations
--   into the current environment.
defineDataDecl :: HS.Decl -> Converter ()
defineDataDecl (HS.DataDecl _ (HS.DeclIdent _ ident) typeVarDecls conDecls) =
  do
    -- TODO detect redefinition and inform when renamed
    let arity = length typeVarDecls
    _ <- renameAndDefineTypeCon ident arity
    mapM_ defineConDecl conDecls

-- | Inserts the given data constructor declaration and its smart constructor
--   into the current environment.
defineConDecl :: HS.ConDecl -> Converter ()
defineConDecl (HS.ConDecl _ (HS.DeclIdent _ ident) argTypes) = do
  -- TODO detect redefinition and inform when renamed
  let arity = length argTypes
  _ <- renameAndDefineCon ident arity
  return ()

-------------------------------------------------------------------------------
-- Type variable declarations                                                --
-------------------------------------------------------------------------------

-- | Converts the declarations of type variables in the head of a data type or
--   type synonym declaration to a Coq binder for a set of explicit or implicit
--   type arguments.
--
--   E.g. the declaration of the type variable @a@ in @data D a = ...@ is
--   translated to the binder @(a : Type)@. If there are multiple type variable
--   declarations as in @data D a b = ...@ they are grouped into a single
--   binder @(a b : Type)@ because we assume all Haskell type variables to be
--   of kind @*@.
--
--   The first argument controlls whether the generated binders are explicit
--   (e.g. @(a : Type)@) or implicit (e.g. @{a : Type}@).
convertTypeVarDecls
  :: G.Explicitness   -- ^ Whether to generate an explicit or implit binder.
  -> [HS.TypeVarDecl] -- ^ The type variable declarations.
  -> Converter [G.Binder]
convertTypeVarDecls explicitness typeVarDecls =
  generateTypeVarDecls' explicitness (map HS.fromDeclIdent typeVarDecls)

-- | Generates explicit or implicit Coq binders for the type variables with
--   the given names that are either declared in the head of a data type or
--   type synonym declaration or occur in the type signature of a function.
--
--   The first argument controlls whether the generated binders are explicit
--   (e.g. @(a : Type)@) or implicit (e.g. @{a : Type}@).
generateTypeVarDecls :: G.Explicitness -> [HS.Name] -> Converter [G.Binder]
generateTypeVarDecls explicitness =
  generateTypeVarDecls' explicitness . catMaybes . map identFromName
 where
  identFromName :: HS.Name -> Maybe HS.TypeVarIdent
  identFromName (HS.Ident  ident) = Just ident
  identFromName (HS.Symbol _    ) = Nothing

-- | Like 'generateTypeVarDecls' but accepts the raw identifiers of the
--   type variables.
generateTypeVarDecls'
  :: G.Explicitness    -- ^ Whether to generate an explicit or implit binder.
  -> [HS.TypeVarIdent] -- ^ The names of the type variables to declare.
  -> Converter [G.Binder]
generateTypeVarDecls' explicitness idents
  | null idents = return []
  | otherwise = do
    -- TODO detect redefinition
    idents' <- mapM renameAndDefineTypeVar idents
    return [G.typedBinder explicitness (map (G.bare) idents') G.sortType]

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | Inserts the given type signature into the current environment.
--
--   TODO error if there are multiple type signatures for the same function.
--   TODO warn if there are unused type signatures.
filterAndDefineTypeSig :: HS.Decl -> Converter ()
filterAndDefineTypeSig (HS.TypeSig _ idents typeExpr) = do
  mapM_
    (modifyEnv . flip defineTypeSig typeExpr . HS.Ident . HS.fromDeclIdent)
    idents
filterAndDefineTypeSig _ = return () -- ignore other declarations.

-- | Looks up the annoated type of a user defined function with the given name
--   and reports a fatal error message if there is no such type signature.
--
--   If an error is encountered, the reported message points to the given
--   source span.
lookupTypeSigOrFail :: SrcSpan -> HS.Name -> Converter HS.Type
lookupTypeSigOrFail srcSpan ident = do
  mTypeExpr <- inEnv $ lookupTypeSig ident
  case mTypeExpr of
    Just typeExpr -> return typeExpr
    Nothing ->
      reportFatal
        $ Message srcSpan Error
        $ ("Missing type signature for " ++ showPretty ident)

-- | Splits the annotated type of a Haskell function with the given arity into
--   its argument and return types.
--
--   A function with arity \(n\) has \(n\) argument types. TODO  Type synonyms
--   are expanded if neccessary.
splitFuncType :: HS.Type -> Int -> Converter ([HS.Type], HS.Type)
splitFuncType (HS.TypeFunc _ t1 t2) arity | arity > 0 = do
  (argTypes, returnType) <- splitFuncType t2 (arity - 1)
  return (t1 : argTypes, returnType)
splitFuncType funcType _ = return ([], funcType)

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Converts a strongly connected component of the function dependency graph.
convertFuncComponent :: DependencyComponent -> Converter [G.Sentence]
convertFuncComponent (NonRecursive decl) = do
  decl' <- convertNonRecFuncDecl decl
  return [decl']
convertFuncComponent (Recursive decls) = convertRecFuncDecls decls

-- | Converts the name, arguments and return type of a function to Coq.
--
--   This code is shared between the conversion functions for recursive and
--   no recursive functions (see 'convertNonRecFuncDecl' and
--   'convertRecFuncDecls').
convertFuncHead
  :: SrcSpan       -- ^ TODO
  -> HS.Name       -- ^ The name of the function.
  -> [HS.VarPat]   -- ^ The function argument patterns.
  -> Converter (G.Qualid, [G.Binder], G.Term)
convertFuncHead srcSpan name args = do
  -- Lookup the Coq name of the function.
  Just qualid            <- inEnv $ lookupIdent VarScope name
    -- Lookup type signature and partiality.
  partial                <- inEnv $ isPartial name
  funcType               <- lookupTypeSigOrFail srcSpan name
  (argTypes, returnType) <- splitFuncType funcType (length args)
  -- Convert arguments and return type.
  typeVarDecls'          <- generateTypeVarDecls G.Implicit (typeVars funcType)
  decArgIndex            <- inEnv $ lookupDecArg name
  args'                  <- convertTypedArgs args argTypes decArgIndex
  returnType'            <- convertType returnType
  return
    ( qualid
    , (  genericArgDecls G.Explicit
      ++ [ partialArgDecl | partial ]
      ++ typeVarDecls'
      ++ args'
      )
    , returnType'
    )

-- | Inserts the given function declaration into the current environment.
defineFuncDecl :: HS.Decl -> Converter ()
defineFuncDecl (HS.FuncDecl _ (HS.DeclIdent _ ident) args _) = do
  -- TODO detect redefinition and inform when renamed
  let arity = length args
  _ <- renameAndDefineFunc ident arity
  return ()

-------------------------------------------------------------------------------
-- Non-recursive function declarations                                       --
-------------------------------------------------------------------------------

-- | Converts a non-recursive Haskell function declaration to a Coq
--   @Definition@ sentence.
convertNonRecFuncDecl :: HS.Decl -> Converter G.Sentence
convertNonRecFuncDecl decl@(HS.FuncDecl _ (HS.DeclIdent srcSpan ident) args expr)
  = do
    defineFuncDecl decl
    localEnv $ do
      let name = HS.Ident ident
      (qualid, binders, returnType') <- convertFuncHead srcSpan name args
      expr'                          <- convertExpr expr
      return (G.definitionSentence qualid binders returnType' expr')

-------------------------------------------------------------------------------
-- Recursive function declarations                                           --
-------------------------------------------------------------------------------

-- | Converts (mutually) recursive Haskell function declarations to Coq.
convertRecFuncDecls :: [HS.Decl] -> Converter [G.Sentence]
convertRecFuncDecls decls = do
  (helperDecls, mainDecls) <- mapAndUnzipM transformRecFuncDecl decls
  fixBodies                <- localEnv $ do
    helperDecls' <- mapM (inlineDecl mainDecls) (concat helperDecls)
    mapM convertRecHelperFuncDecl helperDecls'
  mainFunctions <- mapM convertNonRecFuncDecl mainDecls
  return
    ( -- TODO comment
      G.FixpointSentence (G.Fixpoint (NonEmpty.fromList fixBodies) [])
    : mainFunctions
    )

-- | Identifies the decreasing argument of a function with the given right
--   hand side.
--
--   Returns the name of the decreasing argument.
--
--   TODO the case expression does not have to be the outermost expression.
identifyDecArg :: HS.Expr -> Converter HS.Name
identifyDecArg (HS.Case _ (HS.Var srcSpan decArg) _) = do
  isArg <- inEnv $ not . isFunction decArg
  if isArg
    then return decArg
    else
      reportFatal
      $  Message srcSpan Error
      $  "Expected name of decreasing argument, got function '"
      ++ showPretty decArg
      ++ "'."
identifyDecArg expr =
  reportFatal
    $  Message (HS.getSrcSpan expr) Error
    $  "Outermost expression of recursive function must perform pattern"
    ++ "matching on structurally decreasing argument."

-- | Transforms the given recursive function declaration into recursive
--   helper functions and a non recursive main function.
transformRecFuncDecl :: HS.Decl -> Converter ([HS.Decl], HS.Decl)
transformRecFuncDecl (HS.FuncDecl srcSpan declIdent args expr) = do
  -- Name of original function.
  let name     = HS.Ident (HS.fromDeclIdent declIdent)
      argNames = map (HS.Ident . HS.fromVarPat) args
      arity    = length (args)

  -- Identify decreasing argument of the function.
  decArg <- identifyDecArg expr
  let (Just decArgIndex) = elemIndex decArg argNames

  -- TODO there can be multiple helper functions:

  -- Generate helper function declaration.
  helperIdent <- freshHaskellIdent (HS.fromDeclIdent declIdent)
  let helperName      = HS.Ident helperIdent
      helperDeclIdent = HS.DeclIdent (HS.getSrcSpan declIdent) helperIdent
      helperFuncDecl  = HS.FuncDecl srcSpan helperDeclIdent args expr

  -- Register the helper function to the environment.
  -- The type of the helper function is the same as of the original function.
  -- Additionally we need to remember the index of the decreasing argument
  -- (see 'convertDecArg').
  _        <- renameAndDefineFunc helperIdent arity
  funcType <- lookupTypeSigOrFail srcSpan name
  modifyEnv $ defineTypeSig helperName funcType
  modifyEnv $ defineDecArg helperName decArgIndex

  -- Generate main function declaration.
  let mainExpr = HS.app NoSrcSpan
                        (HS.Var NoSrcSpan helperName)
                        (map (HS.Var NoSrcSpan) argNames)
      mainFuncDecl = HS.FuncDecl srcSpan declIdent args mainExpr

  return ([helperFuncDecl], mainFuncDecl)

-- | Converts a recursive helper function to the body of a Coq @Fixpoint@
--   sentence.
convertRecHelperFuncDecl :: HS.Decl -> Converter G.FixBody
convertRecHelperFuncDecl (HS.FuncDecl srcSpan declIdent args expr) =
  localEnv $ do
    let helperName = HS.Ident (HS.fromDeclIdent declIdent)
    (qualid, binders, returnType') <- convertFuncHead srcSpan helperName args
    expr'                          <- convertExpr expr
    return
      (G.FixBody qualid
                 (NonEmpty.fromList binders)
                 Nothing
                 (Just returnType')
                 expr'
      )

-------------------------------------------------------------------------------
-- Function argument declarations                                            --
-------------------------------------------------------------------------------

-- | Converts the argument of a function (a variable pattern) to an explicit
--   Coq binder whose type is inferred by Coq.
convertInferredArg :: HS.VarPat -> Converter G.Binder
convertInferredArg = flip convertArg Nothing

-- | Converts the argument of a function (a variable pattern) with the given
--   type to an explicit Coq binder.
convertTypedArg :: HS.VarPat -> HS.Type -> Converter G.Binder
convertTypedArg arg argType = do
  argType' <- convertType argType
  convertArg arg (Just argType')

-- | Convert the decreasing argument (variable pattern) if a recursive function
--   with the given type to an explicit Coq binder.
--
--   In contrast to a regular typed argument (see 'convertTypedArg'), the
--   decreasing argument is not lifted to the @Free@ monad.
--   It is also registered as a non-monadic value (see 'definePureVar').
convertDecArg :: HS.VarPat -> HS.Type -> Converter G.Binder
convertDecArg arg argType = do
  argType' <- convertType' argType
  binder   <- convertArg arg (Just argType')
  modifyEnv $ definePureVar (HS.Ident (HS.fromVarPat arg))
  return binder

-- | Converts the arguments (variable patterns) of a potentially recursive
--   function with the given types to explicit Coq binders.
--
--   If the function is recursive, its decreasing argument (given index),
--   is not lifted.
convertTypedArgs
  :: [HS.VarPat] -- ^ The function arguments.
  -> [HS.Type]   -- ^ The types of the function arguments.
  -> Maybe Int   -- ^ The position of the decreasing argument.
  -> Converter [G.Binder]
convertTypedArgs args argTypes Nothing = zipWithM convertTypedArg args argTypes
convertTypedArgs args argTypes (Just index) = do
  bindersBefore <- convertTypedArgs argsBefore argTypesBefore Nothing
  decArgBinder  <- convertDecArg decArg decArgType
  bindersAfter  <- convertTypedArgs argsAfter argTypesAfter Nothing
  return (bindersBefore ++ decArgBinder : bindersAfter)
 where
  (argsBefore    , decArg : argsAfter        ) = splitAt index args
  (argTypesBefore, decArgType : argTypesAfter) = splitAt index argTypes

-- | Converts the argument of a function (a variable pattern) to an explicit
--   Coq binder.
convertArg :: HS.VarPat -> Maybe G.Term -> Converter G.Binder
convertArg (HS.VarPat _ ident) mArgType' = do
  -- TODO detect redefinition.
  ident' <- renameAndDefineVar ident
  generateArgBinder ident' mArgType'

-- | Generates an explicit Coq binder for a function argument with the given
--   name and optional Coq type.
--
--   If no type is provided, it will be inferred by Coq.
generateArgBinder :: String -> Maybe G.Term -> Converter G.Binder
generateArgBinder ident' Nothing =
  return (G.Inferred G.Explicit (G.Ident (G.bare ident')))
generateArgBinder ident' (Just argType') =
  return (G.typedBinder' G.Explicit (G.bare ident') argType')

-- | Converts the argument of an artifically generated function to an explicit
--   Coq binder. A fresh Coq identifier is selected for the argument
--   and returned together with the binder.
convertAnonymousArg :: Maybe HS.Type -> Converter (String, G.Binder)
convertAnonymousArg mArgType = do
  ident'    <- freshCoqIdent freshArgPrefix
  mArgType' <- mapM convertType mArgType
  binder    <- generateArgBinder ident' mArgType'
  return (ident', binder)

-------------------------------------------------------------------------------
-- Type expressions                                                          --
-------------------------------------------------------------------------------

-- | Converts a Haskell type to Coq, lifting it into the @Free@ monad.
--
--   [\(\tau^\dagger = Free\,Shape\,Pos\,\tau^*\)]
--     A type \(\tau\) is converted by lifting it into the @Free@ monad and
--     recursivly converting the argument and return types of functions
--     using 'convertType''.
convertType :: HS.Type -> Converter G.Term
convertType t = do
  t' <- convertType' t
  return (genericApply CoqBase.free [t'])

-- | Converts a Haskell type to Coq.
--
--   In contrast to 'convertType', the type itself is not lifted into the
--   @Free@ moand. Only the argument and return types of contained function
--   type constructors are lifted recursivly.
--
--   [\(\alpha^* = \alpha'\)]
--     A type variable \(\alpha\) is translated by looking up the corresponding
--     Coq identifier \(\alpha'\).
--
--   [\(T^* = T'\,Shape\,Pos\)]
--     A type constructor \(T\) is translated by looking up the corresponding
--     Coq identifier \(T'\) and adding the parameters \(Shape\) and \(Pos\).
--
--   [\((\tau_1\,\tau_2)^* = \tau_1^*\,\tau_2^*\)]
--     Type constructor applications are translated recursively but
--     remain unchanged otherwise.
--
--   [\((\tau_1 \rightarrow \tau_2)^* = \tau_1^\dagger \rightarrow \tau_2^\dagger\)]
--     Type constructor applications are translated recursively but
--     remain unchanged otherwise.
convertType' :: HS.Type -> Converter G.Term
convertType' (HS.TypeVar srcSpan ident) = do
  qualid <- lookupIdentOrFail srcSpan TypeScope (HS.Ident ident)
  return (G.Qualid qualid)
convertType' (HS.TypeCon srcSpan name) = do
  qualid <- lookupIdentOrFail srcSpan TypeScope name
  return (genericApply qualid [])
convertType' (HS.TypeApp _ t1 t2) = do
  t1' <- convertType' t1
  t2' <- convertType' t2
  return (G.app t1' [t2'])
convertType' (HS.TypeFunc _ t1 t2) = do
  t1' <- convertType t1
  t2' <- convertType t2
  return (G.Arrow t1' t2')

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Applies eta-abstractions to a function or constructor application util the
--   function or constructor is fully applied.
--
--   E.g. an application @f x@ of a binary function @f@ will be converted
--   to @\y -> f x y@ where @y@ is a fresh variable. This function does not
--   apply the eta-conversion recursively.
--
--   No eta-conversions are applied to nested expressions.
etaConvert :: HS.Expr -> Converter HS.Expr
etaConvert rootExpr = arityOf rootExpr >>= etaAbstractN rootExpr
 where
  -- | Determines the number of arguments expected to be passed to the given
  --   expression.
  arityOf :: HS.Expr -> Converter Int
  arityOf (HS.Con _ name) = do
    arity <- inEnv $ lookupArity SmartConScope name
    return (maybe 0 id arity)
  arityOf (HS.Var _ name) = do
    arity <- inEnv $ lookupArity VarScope name
    return (maybe 0 id arity)
  arityOf (HS.App _ e1 _) = do
    arity <- arityOf e1
    return (max 0 (arity - 1))
  arityOf _ = return 0

  -- | Applies the given number of eta-abstractions to an expression.
  etaAbstractN :: HS.Expr -> Int -> Converter HS.Expr
  etaAbstractN expr 0 = return expr
  etaAbstractN expr n = do
    x     <- freshHaskellIdent freshArgPrefix
    expr' <- etaAbstractN
      (HS.app NoSrcSpan expr [HS.Var NoSrcSpan (HS.Ident x)])
      (n - 1)
    return (HS.Lambda NoSrcSpan [HS.VarPat NoSrcSpan x] expr')

-- | Converts a Haskell expression to Coq.
convertExpr :: HS.Expr -> Converter G.Term
convertExpr expr = etaConvert expr >>= flip convertExpr' []

-- | Converts the application of a Haskell expression to the given arguments
--   to Coq.
--
--   This function assumes the outer most expression to be fully applied
--   by the given arguments (see also 'etaConvert').
convertExpr' :: HS.Expr -> [HS.Expr] -> Converter G.Term

-- Constructors.
convertExpr' (HS.Con srcSpan name) args = do
  qualid     <- lookupIdentOrFail srcSpan SmartConScope name
  args'      <- mapM convertExpr args
  Just arity <- inEnv $ lookupArity SmartConScope name
  let expectedArgs'   = take arity args'
      additionalArgs' = drop arity args'
  generateApply (genericApply qualid expectedArgs') additionalArgs'

-- Functions and variables.
convertExpr' (HS.Var srcSpan name) args = do
  qualid   <- lookupIdentOrFail srcSpan VarScope name
  args'    <- mapM convertExpr args
  function <- inEnv $ isFunction name
  if function
    then do
      Just arity <- inEnv $ lookupArity VarScope name
      partial    <- inEnv $ isPartial name
      let expectedArgs'   = take arity args'
          additionalArgs' = drop arity args'
          partialArg      = [ G.Qualid (fst CoqBase.partialArg) | partial ]
      generateApply (genericApply qualid (partialArg ++ expectedArgs'))
                    additionalArgs'
    else do
      pureArg <- inEnv $ isPureVar name
      if pureArg
        then generateApply (generatePure (G.Qualid qualid)) args'
        else generateApply (G.Qualid qualid) args'

-- Pass argument from applications to converter for callee.
convertExpr' (HS.App _ e1 e2  ) args = convertExpr' e1 (e2 : args)

-- @if@-expressions.
convertExpr' (HS.If _ e1 e2 e3) []   = do
  e1' <- convertExpr e1
  let bool' = genericApply CoqBase.boolTypeCon []
  generateBind e1' (Just bool') $ \cond -> do
    e2' <- convertExpr e2
    e3' <- convertExpr e3
    return (G.If G.SymmetricIf cond Nothing e2' e3')

-- @case@-expressions.
convertExpr' (HS.Case _ expr alts) [] = do
  expr' <- convertExpr expr
  generateBind expr' Nothing $ \value -> do
    alts' <- mapM convertAlt alts
    return (G.match value alts')

-- Error terms.
convertExpr' (HS.Undefined _) [] = return (G.Qualid CoqBase.partialUndefined)
convertExpr' (HS.ErrorExpr _ msg) [] =
  return (G.app (G.Qualid CoqBase.partialError) [G.string msg])

-- Integer literals.
convertExpr' (HS.IntLiteral _ value) [] =
  return (generatePure (G.InScope (G.Num (fromInteger value)) (G.ident "Z")))

-- Lambda abstractions.
convertExpr' (HS.Lambda _ args expr) [] = localEnv $ do
  args' <- mapM convertInferredArg args
  expr' <- convertExpr expr
  return (foldr (generatePure .: G.Fun . return) expr' args')

-- Application of an expression other than a function or constructor
-- application. (We use an as-pattern for @args@ such that we get a compile
-- time warning when a node is added to the AST that we do not conver above).
convertExpr' expr args@(_ : _) = do
  expr' <- convertExpr' expr []
  args' <- mapM convertExpr args
  generateApply expr' args'

-- | Generates a Coq term for applying a monadic term to the given arguments.
generateApply :: G.Term -> [G.Term] -> Converter G.Term
generateApply term []           = return term
generateApply term (arg : args) = do
  term' <- generateBind term Nothing $ \f -> return (G.app f [arg])
  generateApply term' args

-- | Converts an alternative of a Haskell @case@-expressions to Coq.
convertAlt :: HS.Alt -> Converter G.Equation
convertAlt (HS.Alt _ conPat varPats expr) = localEnv $ do
  conPat' <- convertConPat conPat varPats
  expr'   <- convertExpr expr
  return (G.equation conPat' expr')

-- | Converts a Haskell constructor pattern with the given variable pattern
--   arguments to a Coq pattern.
convertConPat :: HS.ConPat -> [HS.VarPat] -> Converter G.Pattern
convertConPat (HS.ConPat srcSpan ident) varPats = do
  qualid   <- lookupIdentOrFail srcSpan ConScope ident
  varPats' <- mapM convertVarPat varPats
  return (G.ArgsPat qualid varPats')

-- | Converts a Haskell variable pattern to a Coq variable pattern.
convertVarPat :: HS.VarPat -> Converter G.Pattern
convertVarPat (HS.VarPat _ ident) = do
  -- TODO detect redefinition
  ident' <- renameAndDefineVar ident
  return (G.QualidPat (G.bare ident'))

-------------------------------------------------------------------------------
-- Free monad                                                                --
-------------------------------------------------------------------------------

-- | The declarations of type parameters for the @Free@ monad.
--
--   The first argument controlls whether the generated binders are explicit
--   (e.g. @(Shape : Type)@) or implicit (e.g. @{Shape : Type}@).
genericArgDecls :: G.Explicitness -> [G.Binder]
genericArgDecls explicitness =
  map (uncurry (G.typedBinder' explicitness)) CoqBase.freeArgs

-- | An explicit binder for the @Partial@ instance that is passed to partial
--   function declarations.
partialArgDecl :: G.Binder
partialArgDecl = uncurry (G.typedBinder' G.Explicit) CoqBase.partialArg

-- | Smart constructor for the application of a Coq function or (type)
--   constructor that requires the parameters for the @Free@ monad.
genericApply :: G.Qualid -> [G.Term] -> G.Term
genericApply func args = G.app (G.Qualid func) (genericArgs ++ args)
  where genericArgs = map (G.Qualid . fst) CoqBase.freeArgs

-- | Wraps the given Coq term with the @pure@ constructor of the @Free@ monad.
generatePure :: G.Term -> G.Term
generatePure = G.app (G.Qualid CoqBase.freePureCon) . (: [])

-- | Generates a Coq expressions that binds the given value to a fresh variable.
--
--   The generated fresh variable is passed to the given function. It is not
--   visible outside of that function.
--   If the given expression is an application of the @pure@ constructor,
--   no bind will be generated. The wrapped value is passed directly to
--   the given function instead of a fresh variable.
--
--   If the second argument is @Nothing@, the type of the fresh variable is
--   inferred by Coq.
generateBind
  :: G.Term        -- ^ The left hand side of the bind operator.
  -> Maybe G.Term  -- ^ The  Coq type of the value to bind or @Nothing@ if it
                   --   should be inferred by Coq.
  -> (G.Term -> Converter G.Term)
                   -- ^ Converter for the right hand side of the generated
                   --   function. The first argument is the fresh variable.
  -> Converter G.Term
generateBind (G.App (G.Qualid con) ((G.PosArg arg) :| [])) _ generateRHS
  | con == CoqBase.freePureCon = generateRHS arg
generateBind expr' argType' generateRHS = localEnv $ do
  x   <- freshCoqIdent freshArgPrefix
  rhs <- generateRHS (G.Qualid (G.bare x))
  return (G.app (G.Qualid CoqBase.freeBind) [expr', G.fun [x] [argType'] rhs])

-------------------------------------------------------------------------------
-- Error reporting                                                           --
-------------------------------------------------------------------------------

-- | Looks up the Coq identifier for a Haskell function, (type/smart)
--   constructor or (type) variable with the given name or reports a fatal
--   error message if the identifier has not been defined.
--
--   If an error is reported, it points to the given source span.
lookupIdentOrFail
  :: SrcSpan -- ^ The source location where the identifier is requested.
  -> Scope   -- ^ The scope to look the identifier up in.
  -> HS.Name -- ^ The Haskell identifier to look up.
  -> Converter G.Qualid
lookupIdentOrFail srcSpan scope name = do
  mQualid <- inEnv $ lookupIdent scope name
  case mQualid of
    Just qualid -> return qualid
    Nothing ->
      reportFatal
        $ Message srcSpan Error
        $ ("Unknown " ++ showPretty scope ++ ": " ++ showPretty name)
