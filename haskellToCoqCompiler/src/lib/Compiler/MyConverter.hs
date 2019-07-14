-- | This module contains the new implementation of the converter from
--   Haskell to Coq using the @Free@ monad.
--
--   TODO rename to @Compiler.Converter@

module Compiler.MyConverter where

import           Control.Monad                  ( mapAndUnzipM )
import           Data.Maybe                     ( maybe
                                                , catMaybes
                                                )

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Converter.State
import           Compiler.Converter.Renamer
import qualified Compiler.Language.Coq.AST     as G
import qualified Compiler.Language.Coq.Base    as CoqBase
import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.Pretty
import           Compiler.Reporter
import           Compiler.SrcSpan
import           Compiler.Util.Control.Monad
import           Compiler.Util.Data.List.NonEmpty

-- | Initially the environment contains the predefined functions, data types
--   and their constructors from the Coq Base library that accompanies this
--   compiler.
defaultEnvironment :: Environment
defaultEnvironment = CoqBase.predefine emptyEnvironment

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Converts a Haskell module to a Gallina module sentence.
--
--   If no module header is present the generated module is called @"Main"@.
-- TODO add preamble
convertModule :: HS.Module -> Converter G.Sentence
convertModule (HS.Module _ maybeIdent decls) = do
  let modName = G.ident (maybe "Main" id maybeIdent)
  decls' <- convertDecls decls
  return (G.LocalModuleSentence (G.LocalModule modName decls'))

-- | Converts the declarations from a Haskell module to Coq.
convertDecls :: [HS.Decl] -> Converter [G.Sentence]
convertDecls decls = concatMapM convertTypeComponent components
  where components = groupDeclarations decls

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
--   not be able to depend on each other.
--
--   After the @Inductive@ sentences for the data type declarations there
--   is one argument sentence for each constructor declaration.
convertDataDecls :: [HS.Decl] -> Converter [G.Sentence]
convertDataDecls dataDecls = do
  mapM_ defineDataDecl dataDecls
  (indBodies, extraSentences) <- mapAndUnzipM convertDataDecl dataDecls
  return
    ( G.InductiveSentence (G.Inductive (toNonEmptyList indBodies) [])
    : concat extraSentences
    )
-- TODO Smart Constructors

-- | Converts a Haskell data type declaration to the body of a Coq @Inductive@
--   sentence and the @Arguments@ sentences for it's constructors.
--
--   This function assumes, that the identifiers for the declared data type
--   and it's constructors are defined already (see 'defineDataDecl').
--   Type variables declared by the data type declaration are not visible
--   outside this function (this is why the @Arguments@ sentences need to
--   be generated here).
convertDataDecl :: HS.Decl -> Converter (G.IndBody, [G.Sentence])
convertDataDecl (HS.DataDecl srcSpan (HS.DeclIdent _ ident) typeVarDecls conDecls)
  = localEnv $ do
    -- Inductive sentence:
    Just qualid   <- inEnv $ lookupTypeCon (HS.Ident ident)
    typeVarDecls' <- convertTypeVarDecls typeVarDecls
    -- Constructor declarations:
    returnType    <- convertType' $ HS.typeApp
      srcSpan
      (HS.Ident ident)
      (map (HS.TypeVar srcSpan . fromDeclIdent) typeVarDecls)
    conDecls'          <- mapM (convertConDecl returnType) conDecls
    -- Arguments sentences:
    argumentSpecs      <- generateArgumentSpecs typeVarDecls
    argumentsSentences <- mapM (generateArgumentsSentence argumentSpecs)
                               conDecls
    return
      ( G.IndBody qualid (genericArgDecls ++ typeVarDecls') G.sortType conDecls'
      , argumentsSentences
      )

-- | Converts the declarations of type variables in the head of a data type or
--   type synonym declaration to a Coq binder for a set of explicit type
--   arguments.
--
--   E.g. the declaration of the type variable @a@ in @data D a = ...@ is
--   translated to the binder @(a : Type)@. If there are multiple type variable
--   declarations as in @data D a b = ...@ they are grouped into a single
--   binder @(a b : Type)@ because we assume all Haskell type variables to be
--   of kind @*@.
convertTypeVarDecls :: [HS.TypeVarDecl] -> Converter [G.Binder]
convertTypeVarDecls []           = return []
convertTypeVarDecls typeVarDecls = do
  -- TODO detect redefinition
  let idents = map fromDeclIdent typeVarDecls
  idents' <- mapM renameAndDefineTypeVar idents
  return
    [ G.Typed G.Ungeneralizable
              G.Explicit
              (toNonEmptyList (map (G.Ident . G.bare) idents'))
              G.sortType
    ]

-- | Inserts the given data type declaration and its constructor declarations
--   into the current environment.
defineDataDecl :: HS.Decl -> Converter ()
defineDataDecl (HS.DataDecl _ (HS.DeclIdent _ ident) _ conDecls) = do
  -- TODO detect redefinition and inform when renamed
  _ <- renameAndDefineTypeCon ident
  mapM_ defineConDecl conDecls

-------------------------------------------------------------------------------
-- Data constructor declarations                                             --
-------------------------------------------------------------------------------

-- | Converts a Haskell data constructor declaration.
--
--   This function assumes, that the identifier for the constructor was defined
--   already (see 'defineConDecl').
convertConDecl
  :: G.Term     -- ^ The Coq type produced by the constructor.
  -> HS.ConDecl -- ^ The constructor to convert.
  -> Converter (G.Qualid, [G.Binder], Maybe G.Term)
convertConDecl returnType (HS.ConDecl _ (HS.DeclIdent _ ident) args) = do
  Just qualid <- inEnv $ lookupCon (HS.Ident ident)
  args'       <- mapM convertType args
  return (qualid, [], Just (args' `G.arrows` returnType))

-- | Inserts the given data constructor declaration into the current
--   environment.
defineConDecl :: HS.ConDecl -> Converter ()
defineConDecl (HS.ConDecl _ (HS.DeclIdent _ ident) _) = do
  -- TODO detect redefinition and inform when renamed
  _ <- renameAndDefineCon ident
  return ()

-------------------------------------------------------------------------------
-- Arguments sentences                                                       --
-------------------------------------------------------------------------------

-- | Generates @G.ArgumentSpec@s that mark the generic arguments for the @Free@
--   monad as well as the type variables in the given list as implicit.
generateArgumentSpecs :: [HS.TypeVarDecl] -> Converter [G.ArgumentSpec]
generateArgumentSpecs typeVarDecls = do
  let typeVarIdents = map (HS.Ident . fromDeclIdent) typeVarDecls
  typeVarQualids <- mapM (inEnv . lookupTypeVar) typeVarIdents
  return
    [ G.ArgumentSpec G.ArgMaximal (G.Ident typeVarQualid) Nothing
    | typeVarQualid <- map fst CoqBase.freeArgs ++ catMaybes typeVarQualids
    ]

-- | Generates the @Arguments@ sentence for a constructor declaration.
generateArgumentsSentence
  :: [G.ArgumentSpec] -> HS.ConDecl -> Converter G.Sentence
generateArgumentsSentence specs (HS.ConDecl _ (HS.DeclIdent _ ident) _) = do
  Just qualid <- inEnv $ lookupCon (HS.Ident ident)
  return (G.ArgumentsSentence (G.Arguments Nothing qualid specs))

-------------------------------------------------------------------------------
-- Type expressions                                                          --
-------------------------------------------------------------------------------

-- | Converts a Haskell type to Coq, lifting it into the @Free@ monad.
--
--   This is the implementation of the @†@ translation for types.
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
--   This is the implementation of the @*@ translation for types.
convertType' :: HS.Type -> Converter G.Term
convertType' (HS.TypeVar srcSpan ident) = do
  mQualid <- inEnv $ lookupTypeVar (HS.Ident ident)
  case mQualid of
    Nothing     -> unknownTypeVarError srcSpan ident
    Just qualid -> return (G.Qualid qualid)
convertType' (HS.TypeCon srcSpan name) = do
  mQualid <- inEnv $ lookupTypeCon name
  case mQualid of
    Nothing     -> unknownTypeConError srcSpan name
    Just qualid -> return (genericApply qualid [])
convertType' (HS.TypeApp _ t1 t2) = do
  t1' <- convertType' t1
  t2' <- convertType' t2
  return (G.app t1' [t2'])
convertType' (HS.TypeFunc _ t1 t2) = do
  t1' <- convertType t1
  t2' <- convertType t2
  return (G.Arrow t1' t2')

-------------------------------------------------------------------------------
-- Utility functions                                                         --
-------------------------------------------------------------------------------

-- | Extracts the actual identifier from an identifier in a declaration.
fromDeclIdent :: HS.DeclIdent -> String
fromDeclIdent (HS.DeclIdent _ ident) = ident

-------------------------------------------------------------------------------
-- Free monad arguments                                                      --
-------------------------------------------------------------------------------

-- | The declarations of type parameters for the
genericArgDecls :: [G.Binder]
genericArgDecls = map (uncurry genericArgDecl) CoqBase.freeArgs
 where
  genericArgDecl :: G.Qualid -> G.Term -> G.Binder
  genericArgDecl = G.Typed G.Ungeneralizable G.Explicit . singleton . G.Ident

-- | Smart constructor for the application of a Coq function or (type)
--   constructor that requires the parameters for the @Free@ monad.
genericApply :: G.Qualid -> [G.Term] -> G.Term
genericApply func args = G.app (G.Qualid func) (genericArgs ++ args)
  where genericArgs = map (G.Qualid . fst) CoqBase.freeArgs

-------------------------------------------------------------------------------
-- Error reporting                                                           --
-------------------------------------------------------------------------------

-- | Reports a fatal error message when an unknown type constructor is
--   encountered.
unknownTypeConError :: SrcSpan -> HS.Name -> Converter a
unknownTypeConError srcSpan name = reportFatal $ Message
  (Just srcSpan)
  Error
  ("Unknown type constructor: " ++ showPretty name)

-- | Reports a fatal error message when an unknown type variable is
--   encountered.
--
--   This could happen if a type variable is used in a data constructor
--   that was not declaraed in the data type declaration's head.
unknownTypeVarError :: SrcSpan -> HS.TypeVarIdent -> Converter a
unknownTypeVarError srcSpan ident = reportFatal
  $ Message (Just srcSpan) Error ("Unknown type variable: " ++ ident)
