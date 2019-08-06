-- | This module contains functions for converting type synonym and data type
--   declarations and their constructors.

module Compiler.Converter.TypeDecl where

import           Control.Monad                  ( mapAndUnzipM )
import           Control.Monad.Extra            ( concatMapM )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( catMaybes )
import           Data.List                      ( partition )
import qualified Data.List.NonEmpty            as NonEmpty

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Environment
import           Compiler.Converter.Arg
import           Compiler.Converter.Free
import           Compiler.Converter.Type
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Environment
import           Compiler.Environment.Renamer
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Inliner
import           Compiler.Monad.Converter

-------------------------------------------------------------------------------
-- Strongly connected components                                             --
-------------------------------------------------------------------------------

-- | Converts a strongly connected component of the type dependency graph.
convertTypeComponent :: DependencyComponent -> Converter [G.Sentence]
convertTypeComponent (NonRecursive decl)
  | isTypeDecl decl = defineTypeDecl decl >> convertTypeDecl decl
  | otherwise       = convertDataDecls [decl]
convertTypeComponent (Recursive decls) = do
  let (typeDecls, dataDecls) = partition isTypeDecl decls
  dataDecls' <- withTypeSynonyms typeDecls $ do
    expandedDataDecls <- mapM expandAllTypeSynonymsInDecl dataDecls
    convertDataDecls expandedDataDecls
  typeDecls' <- concatMapM convertTypeDecl typeDecls -- TODO sort topologically
  return (dataDecls' ++ typeDecls')
 where
  -- | Creates a converter that runs the given converter in an environment that
  --   contains only the type synonyms from the given type synonym
  --   declarations.
  --
  --   The resulting environment contains both the old and the given type
  --   synonym declarations.
  withTypeSynonyms :: [HS.Decl] -> Converter a -> Converter a
  withTypeSynonyms typeDecls converter = do
    oldTypeSynonyms <- inEnv definedTypeSynonyms
    modifyEnv $ \env ->
      env { definedTypeSynonyms = definedTypeSynonyms emptyEnvironment }
    mapM defineTypeDecl typeDecls
    x <- converter
    modifyEnv $ \env -> env
      { definedTypeSynonyms = definedTypeSynonyms env
                                `Map.union` oldTypeSynonyms
      }
    return x

-------------------------------------------------------------------------------
-- Type synonym declarations                                                 --
-------------------------------------------------------------------------------

-- | Tests whether the given declaration is a type synonym declaration.
isTypeDecl :: HS.Decl -> Bool
isTypeDecl (HS.TypeDecl _ _ _ _) = True
isTypeDecl _                     = False

-- | Inserts the given type synonym declaration into the current environment.
defineTypeDecl :: HS.Decl -> Converter ()
defineTypeDecl (HS.TypeDecl _ declIdent typeVarDecls typeExpr) = do
  let ident    = HS.fromDeclIdent declIdent
      name     = HS.Ident ident
      arity    = length typeVarDecls
      typeVars = map HS.fromDeclIdent typeVarDecls
  ident' <- renameAndDefineTypeCon ident arity
  modifyEnv $ defineTypeSynonym name typeVars typeExpr

-- | Converts a Haskell type synonym declaration to Coq.
convertTypeDecl :: HS.Decl -> Converter [G.Sentence]
convertTypeDecl (HS.TypeDecl _ declIdent typeVarDecls typeExpr) = localEnv $ do
  let ident = HS.fromDeclIdent declIdent
      name  = HS.Ident ident
  Just qualid   <- inEnv $ lookupIdent TypeScope name
  typeVarDecls' <- convertTypeVarDecls G.Explicit typeVarDecls
  typeExpr'     <- convertType' typeExpr
  return
    [ G.definitionSentence qualid
                           (genericArgDecls G.Explicit ++ typeVarDecls')
                           (Just G.sortType)
                           typeExpr'
    ]

-------------------------------------------------------------------------------
-- Data type declarations                                                    --
-------------------------------------------------------------------------------

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
convertDataDecl decl@(HS.DataDecl _ (HS.DeclIdent _ ident) typeVarDecls conDecls)
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
  returnType = conReturnType decl

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
    rhs         <- generatePure
      (G.app (G.Qualid qualid) (map (G.Qualid . G.bare) argIdents'))
    return
      (G.definitionSentence
        smartQualid
        (genericArgDecls G.Explicit ++ typeVarDecls' ++ argDecls')
        (Just returnType')
        rhs
      )

-- | Inserts the given data type declaration and its constructor declarations
--   into the current environment.
defineDataDecl :: HS.Decl -> Converter ()
defineDataDecl decl@(HS.DataDecl _ declIdent typeVarDecls conDecls) = do
    -- TODO detect redefinition and inform when renamed
  let arity = length typeVarDecls
  _ <- renameAndDefineTypeCon (HS.fromDeclIdent declIdent) arity
  mapM_ defineConDecl conDecls
 where
  -- | The type produced by all constructors of the data type.
  returnType :: HS.Type
  returnType = conReturnType decl

  -- | Inserts the given data constructor declaration and its smart constructor
  --   into the current environment.
  defineConDecl :: HS.ConDecl -> Converter ()
  defineConDecl (HS.ConDecl _ (HS.DeclIdent _ conIdent) argTypes) = do
    -- TODO detect redefinition and inform when renamed
    _ <- renameAndDefineCon conIdent (map Just argTypes) (Just returnType)
    return ()

-- | Gets the Haskell return type of the constructors for the given data type
--   declaration.
conReturnType :: HS.Decl -> HS.Type
conReturnType (HS.DataDecl srcSpan (HS.DeclIdent _ ident) typeVarDecls _) =
  HS.typeApp srcSpan
             (HS.Ident ident)
             (map (HS.TypeVar srcSpan . HS.fromDeclIdent) typeVarDecls)
