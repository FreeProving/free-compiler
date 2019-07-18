-- | This module contains the new implementation of the converter from
--   Haskell to Coq using the @Free@ monad.

module Compiler.Converter where

import           Control.Monad                  ( mapAndUnzipM )
import           Control.Monad.Extra            ( concatMapM )
import           Data.Maybe                     ( maybe
                                                , catMaybes
                                                )
import qualified Data.List.NonEmpty            as NonEmpty

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
    Just qualid        <- inEnv $ lookupTypeCon (HS.Ident ident)
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
    Just conQualid <- inEnv $ lookupCon (HS.Ident conIdent)
    args'          <- mapM convertType args
    returnType'    <- convertType' returnType
    return (conQualid, [], Just (args' `G.arrows` returnType'))

  -- | Generates the @Arguments@ sentence for the given constructor declaration.
  generateArgumentsSentence :: HS.ConDecl -> Converter G.Sentence
  generateArgumentsSentence (HS.ConDecl _ (HS.DeclIdent _ conIdent) _) = do
    Just qualid <- inEnv $ lookupCon (HS.Ident conIdent)
    let typeVarIdents = map (HS.Ident . fromDeclIdent) typeVarDecls
    typeVarQualids <- mapM (inEnv . lookupTypeVar) typeVarIdents
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
  generateSmartConDecl (HS.ConDecl _ (HS.DeclIdent _ conIdent) argTypes) =
    localEnv $ do
      Just qualid             <- inEnv $ lookupCon (HS.Ident conIdent)
      Just smartQualid        <- inEnv $ lookupSmartCon (HS.Ident conIdent)
      typeVarDecls'           <- convertTypeVarDecls G.Implicit typeVarDecls
      (argIdents', argDecls') <- mapAndUnzipM convertAnonymousArg argTypes
      returnType'             <- convertType returnType
      return
        (G.DefinitionSentence
          (G.DefinitionDef
            G.Global
            smartQualid
            (genericArgDecls G.Implicit ++ typeVarDecls' ++ argDecls')
            (Just returnType')
            (G.app
              (G.Qualid CoqBase.freePureCon)
              [G.app (G.Qualid qualid) (map (G.Qualid . G.bare) argIdents')]
            )
          )
        )

-- | Inserts the given data type declaration and its constructor declarations
--   into the current environment.
defineDataDecl :: HS.Decl -> Converter ()
defineDataDecl (HS.DataDecl _ (HS.DeclIdent _ ident) _ conDecls) = do
  -- TODO detect redefinition and inform when renamed
  _ <- renameAndDefineTypeCon ident
  mapM_ defineConDecl conDecls

-- | Inserts the given data constructor declaration and its smart constructor
--   into the current environment.
defineConDecl :: HS.ConDecl -> Converter ()
defineConDecl (HS.ConDecl _ (HS.DeclIdent _ ident) _) = do
  -- TODO detect redefinition and inform when renamed
  _ <- renameAndDefineCon ident
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
  :: G.Explicitness -> [HS.TypeVarDecl] -> Converter [G.Binder]
convertTypeVarDecls explicitness typeVarDecls
  | null typeVarDecls = return []
  | otherwise = do
  -- TODO detect redefinition
    let idents = map fromDeclIdent typeVarDecls
    idents' <- mapM renameAndDefineTypeVar idents
    return
      [ G.Typed G.Ungeneralizable
                explicitness
                (NonEmpty.fromList (map (G.Ident . G.bare) idents'))
                G.sortType
      ]

-------------------------------------------------------------------------------
-- Function argument declarations                                            --
-------------------------------------------------------------------------------

-- | Converts the argument of a function (a variable pattern) to an explicit
--   Coq binder.
convertArg :: HS.VarPat -> HS.Type -> Converter G.Binder
convertArg (HS.VarPat _ ident) argType = do
  -- TODO detect redefinition.
  ident' <- renameAndDefineVar ident
  convertArg' ident' argType

-- | Converts an argument (with the given Coq identifier) of a function to
--   an explicit Coq binder.
convertArg' :: String -> HS.Type -> Converter G.Binder
convertArg' ident' argType = do
  argType' <- convertType argType
  return
    (G.Typed G.Ungeneralizable
             G.Explicit
             (return (G.Ident (G.bare ident')))
             argType'
    )

-- | Converts the argument of an artifically generated function to an explicit
--   Coq binder. A fresh Coq identifier is selected for the argument
--   and returned together with the binder.
convertAnonymousArg :: HS.Type -> Converter (String, G.Binder)
convertAnonymousArg argType = do
  ident' <- freshIdent
  binder <- convertArg' ident' argType
  return (ident', binder)

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

-- | The declarations of type parameters for the @Free@ monad.
--
--   The first argument controlls whether the generated binders are explicit
--   (e.g. @(Shape : Type)@) or implicit (e.g. @{Shape : Type}@).
genericArgDecls :: G.Explicitness -> [G.Binder]
genericArgDecls explicitness = map (uncurry genericArgDecl) CoqBase.freeArgs
 where
  genericArgDecl :: G.Qualid -> G.Term -> G.Binder
  genericArgDecl = G.Typed G.Ungeneralizable explicitness . return . G.Ident

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
