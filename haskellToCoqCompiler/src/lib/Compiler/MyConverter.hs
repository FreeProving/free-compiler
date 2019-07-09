-- | This module contains the new implementation of the converter from
--   Haskell to Coq using the @Free@ monad.
--
--   TODO rename to @Compiler.Converter@

module Compiler.MyConverter where

import           Data.Maybe                     ( maybe )

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
  let modName    = G.ident (maybe "Main" id maybeIdent)
      components = groupDeclarations decls
  sentences <- mapM convertTypeComponent components >>= return . concat
  return (G.LocalModuleSentence (G.LocalModule modName sentences))

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
convertDataDecls :: [HS.Decl] -> Converter [G.Sentence]
convertDataDecls dataDecls = do
  -- TODO the types need to be defined and renamed here already, otherwise
  --      they cannot be mutually recursive.
  indBodies <- mapM convertDataDecl dataDecls
  return [G.InductiveSentence (G.Inductive (toNonEmptyList indBodies) [])]
  -- TODO Arguments
  -- TODO Smart Constructors

convertDataDecl :: HS.Decl -> Converter G.IndBody
convertDataDecl (HS.DataDecl srcSpan (HS.DeclIdent _ ident) typeVarDecls conDecls)
  = do
    -- TODO detect redefinition
    ident'        <- renameAndDefineTypeCon ident
    typeVarDecls' <- convertTypeVarDecls typeVarDecls
    returnType    <- convertType' $ HS.typeApp
      srcSpan
      (HS.Ident ident)
      (map (HS.TypeVar srcSpan . fromDeclIdent) typeVarDecls)
    conDecls' <- mapM (convertConDecl returnType) conDecls
    return
      (G.IndBody (G.bare ident')
                 (genericArgDecls ++ typeVarDecls')
                 G.sortType
                 conDecls'
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
convertTypeVarDecls [] = return []
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

-- | Converts a Haskell data constructor declaration.
convertConDecl
  :: G.Term     -- ^ The Coq type produced by the constructor.
  -> HS.ConDecl -- ^ The constructor to convert.
  -> Converter (G.Qualid, [G.Binder], Maybe G.Term)
convertConDecl returnType (HS.ConDecl _ (HS.DeclIdent _ ident) args) = do
  -- TODO detect redefinition
  ident' <- renameAndDefineCon ident
  args'  <- mapM convertType args
  return (G.bare ident', [], Just (args' `G.arrows` returnType))

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
unknownTypeConError srcSpan name = liftReporter $ reportFatal $ Message
  (Just srcSpan)
  Error
  ("Unknown type constructor: " ++ showPretty name)

-- | Reports a fatal error message when an unknown type variable is
--   encountered.
--
--   This could happen if a type variable is used in a data constructor
--   that was not declaraed in the data type declaration's head.
unknownTypeVarError :: SrcSpan -> HS.TypeVarIdent -> Converter a
unknownTypeVarError srcSpan ident = liftReporter $ reportFatal $ Message
  (Just srcSpan)
  Error
  ("Unknown type variable: " ++ ident)
