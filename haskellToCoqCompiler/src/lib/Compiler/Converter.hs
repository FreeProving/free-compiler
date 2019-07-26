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
import qualified Data.List.NonEmpty            as NonEmpty

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyGraph
import           Compiler.Analysis.DependencyExtraction
import           Compiler.Analysis.PartialityAnalysis
import           Compiler.Converter.Fresh
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
    ( G.InductiveSentence (G.Inductive (NonEmpty.fromList indBodies) [])
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
    (map (HS.TypeVar srcSpan . fromDeclIdent) typeVarDecls)

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
    let typeVarIdents = map (HS.Ident . fromDeclIdent) typeVarDecls
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
    let conIdent = HS.Ident (fromDeclIdent declIdent)
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
  generateTypeVarDecls' explicitness (map fromDeclIdent typeVarDecls)

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
  mapM_ (modifyEnv . flip defineTypeSig typeExpr . HS.Ident . fromDeclIdent)
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
        $ Message (Just srcSpan) Error
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
convertFuncComponent (NonRecursive decl) = convertNonRecFuncDecl decl
convertFuncComponent (Recursive decls) =
  error "convertFuncComponent: recursive functions not yet implemented."

-------------------------------------------------------------------------------
-- Non-recursive function declarations                                       --
-------------------------------------------------------------------------------

-- | Converts a non-recursive Haskell function declaration to a Coq
--   @Definition@ sentence.
convertNonRecFuncDecl :: HS.Decl -> Converter [G.Sentence]
convertNonRecFuncDecl (HS.FuncDecl _ (HS.DeclIdent srcSpan ident) args expr) =
  do
    -- Define function.
    let arity = length args
    ident'                 <- renameAndDefineFunc ident arity
    -- Lookup type signature and partiality.
    partial                <- inEnv $ isPartial (HS.Ident ident)
    funcType               <- lookupTypeSigOrFail srcSpan (HS.Ident ident)
    (argTypes, returnType) <- splitFuncType funcType arity
    -- Convert function.
    localEnv $ do
      typeVarDecls' <- generateTypeVarDecls G.Implicit (typeVars funcType)
      args'         <- zipWithM convertTypedArg args argTypes
      returnType'   <- convertType returnType
      expr'         <- convertExpr expr
      return
        [ G.definitionSentence
            (G.bare ident')
            (  genericArgDecls G.Explicit
            ++ [ partialArgDecl | partial ]
            ++ typeVarDecls'
            ++ args'
            )
            returnType'
            expr'
        ]

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
convertTypedArg = flip (flip convertArg . Just)

-- | Converts the argument of a function (a variable pattern) to an explicit
--   Coq binder.
convertArg :: HS.VarPat -> Maybe HS.Type -> Converter G.Binder
convertArg (HS.VarPat _ ident) mArgType = do
  -- TODO detect redefinition.
  ident' <- renameAndDefineVar ident
  convertArg' ident' mArgType

-- | Converts an argument (with the given Coq identifier) of a function to
--   an explicit Coq binder.
convertArg' :: String -> Maybe HS.Type -> Converter G.Binder
convertArg' ident' Nothing =
  return (G.Inferred G.Explicit (G.Ident (G.bare ident')))
convertArg' ident' (Just argType) = do
  argType' <- convertType argType
  return (G.typedBinder' G.Explicit (G.bare ident') argType')

-- | Converts the argument of an artifically generated function to an explicit
--   Coq binder. A fresh Coq identifier is selected for the argument
--   and returned together with the binder.
convertAnonymousArg :: Maybe HS.Type -> Converter (String, G.Binder)
convertAnonymousArg mArgType = do
  ident'    <- freshCoqIdent freshArgPrefix
  binder <- convertArg' ident' mArgType
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

-- | Converts a Haskell expression to Coq.
convertExpr :: HS.Expr -> Converter G.Term
convertExpr expr = convertExpr' expr >>= uncurry etaConvert
 where
  -- | Performs the given number of eta conversions of the given Coq term.
  etaConvert :: G.Term -> Int -> Converter G.Term
  etaConvert term 0     = return term
  etaConvert term arity = do
    x     <- freshCoqIdent freshArgPrefix
    term' <- etaConvert (G.app term [G.Qualid (G.bare x)]) (arity - 1)
    return (generatePure (G.fun [x] [Nothing] term'))

-- | Converts a Haskell expression to Coq and returns besides the converted
--   expression the number of arguments it still needs to be applied to.
--
--   When a defined function is applied partially, the returned function is
--   not wrapped with the @Free@ monad. This is an optimization to make
--   generated function applications more readable (it avoids unwrapping
--   intermediate monadic values in case of fully applied functions). We can
--   apply this optimization because we know that the partial application of a
--   function never fails.
--
--   If the second component of the returned pair is @0@, the expression (first
--   component) does not expect more arguments (regarding the optimization
--   described above) and can be returned directly by 'convertExpr'. Otherwise
--   'convertExpr' needs to perform an eta-conversion i.e. wrap the returned
--   expression with one lambda abstraction @pure (fun x => ...))@ and apply
--   the fresh variable @x@ to the returned expression for every missing
--   argument.
convertExpr' :: HS.Expr -> Converter (G.Term, Int)

-- Constructors.
convertExpr' (HS.Con srcSpan name) = do
  qualid     <- lookupIdentOrFail srcSpan SmartConScope name
  Just arity <- inEnv $ lookupArity SmartConScope name
  return (genericApply qualid [], arity)

-- Functions and variables.
convertExpr' (HS.Var srcSpan name) = do
  qualid <- lookupIdentOrFail srcSpan VarScope name
  -- Lookup arity of function. If there is no such entry, this is not
  -- a function but a variable. Variables do not need the @Shape@ and
  -- @Pos@ arguments.
  mArity <- inEnv $ lookupArity VarScope name
  case mArity of
    Nothing    -> return (G.Qualid qualid, 0)
    Just arity -> do
      partial <- inEnv $ isPartial name
      return
        ( genericApply qualid [ G.Qualid (fst CoqBase.partialArg) | partial ]
        , arity
        )

-- If the callee is a partially applied function or constructor that still
-- expects arguments, we can apply it directly. Otherwise it will be a monadic
-- value and we need to bind the contained function first.
convertExpr' (HS.App _ e1 e2) = do
  (e1', arity) <- convertExpr' e1
  e2'          <- convertExpr e2
  if arity == 0
    then generateBind' e1' Nothing $ \f -> return (G.app (G.Qualid f) [e2'])
    else return (G.app e1' [e2'], arity - 1)

-- @if@-expressions.
convertExpr' (HS.If _ e1 e2 e3) = do
  e1' <- convertExpr e1
  let bool' = genericApply CoqBase.boolTypeCon []
  generateBind' e1' (Just bool') $ \cond -> do
    e2' <- convertExpr e2
    e3' <- convertExpr e3
    return (G.If G.SymmetricIf (G.Qualid cond) Nothing e2' e3')

-- @case@-expressions.
convertExpr' (HS.Case _ expr alts) = do
  expr' <- convertExpr expr
  generateBind' expr' Nothing $ \value -> do
    alts' <- mapM convertAlt alts
    return (G.match (G.Qualid value) alts')

-- Error terms.
convertExpr' (HS.Undefined _) = return (G.Qualid CoqBase.partialUndefined, 0)
convertExpr' (HS.ErrorExpr _ msg) =
  return (G.app (G.Qualid CoqBase.partialError) [G.string msg], 0)

-- Integer literals.
convertExpr' (HS.IntLiteral _ value) =
  return (generatePure (G.InScope (G.Num (fromInteger value)) (G.ident "Z")), 0)

-- Lambda abstractions.
convertExpr' (HS.Lambda _ args expr) = localEnv $ do
  args' <- mapM convertInferredArg args
  expr' <- convertExpr expr
  return (foldr (generatePure .: G.Fun . return) expr' args', 0)

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
-- Utility functions                                                         --
-------------------------------------------------------------------------------

-- | Extracts the actual identifier from an identifier in a declaration.
fromDeclIdent :: HS.DeclIdent -> String
fromDeclIdent (HS.DeclIdent _ ident) = ident

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

generatePure :: G.Term -> G.Term
generatePure = G.app (G.Qualid CoqBase.freePureCon) . (: [])

-- | Generates a Coq expressions that binds the given value to a fresh variable.
--
--   The generated fresh variable is passed to the given function. It is not
--   visible outside of that function.
--
--   If the second argument is @Nothing@, the type of the fresh variable is
--   inferred by Coq.
generateBind
  :: G.Term        -- ^ The left hand side of the bind operator.
  -> Maybe G.Term  -- ^ The  Coq type of the value to bind or @Nothing@ if it
                   --   should be inferred by Coq.
  -> (G.Qualid -> Converter G.Term)
                   -- ^ Converter for the right hand side of the generated
                   --   function. The first argument is the fresh variable.
  -> Converter G.Term
generateBind expr' argType' generateRHS = localEnv $ do
  f   <- freshCoqIdent
  rhs <- generateRHS (G.bare f)
  return (G.app (G.Qualid CoqBase.freeBind) [expr', G.fun [f] [argType'] rhs])

-- | Like 'generateBind', but the return type is compatible
--   with 'convertExpr''.
generateBind'
  :: G.Term
  -> Maybe G.Term
  -> (G.Qualid -> Converter G.Term)
  -> Converter (G.Term, Int)
generateBind' expr' argType' generateRHS = do
  res <- generateBind expr' argType' generateRHS
  return (res, 0)

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
        $ Message (Just srcSpan) Error
        $ ("Unknown " ++ showPretty scope ++ ": " ++ showPretty name)
