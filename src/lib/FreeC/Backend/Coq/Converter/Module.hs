-- | This module contains functions for converting Haskell modules to Coq.

module FreeC.Backend.Coq.Converter.Module where

import           Control.Monad                  ( (>=>) )
import           Control.Monad.Extra            ( concatMapM )
import           Data.List                      ( find
                                                , findIndex
                                                )

import qualified FreeC.Backend.Coq.Base        as Coq.Base
import           FreeC.Backend.Coq.Converter.FuncDecl
import           FreeC.Backend.Coq.Converter.TypeDecl
import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment
import           FreeC.Environment.ModuleInterface
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pipeline
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Converts a Haskell module to a Gallina sentences.
convertModule :: IR.Module -> Converter [Coq.Sentence]
convertModule = moduleEnv . (runPipeline >=> convertModule')

-- | Like 'convertModule'' but does not apply any compiler passes beforehand.
convertModule' :: IR.Module -> Converter [Coq.Sentence]
convertModule' haskellAst = do
  imports' <- convertImportDecls (IR.modImports haskellAst)
  mapM_ (addDecArgPragma (IR.modFuncDecls haskellAst))
        (IR.modPragmas haskellAst)
  decls' <- convertDecls (IR.modTypeDecls haskellAst)
                         (IR.modFuncDecls haskellAst)
  return (Coq.comment ("module " ++ IR.modName haskellAst) : imports' ++ decls')

-------------------------------------------------------------------------------
-- Pragmas                                                                   --
-------------------------------------------------------------------------------

-- | Inserts the decreasing argument's index annotated by the given pragma
--   into the environment.
--
--   Decreasing arguments can be annotated for all function declarations
--   in the current module (first argument).
--
--   All other pragmas are ignored.
addDecArgPragma :: [IR.FuncDecl] -> IR.Pragma -> Converter ()
addDecArgPragma funcDecls (IR.DecArgPragma srcSpan funcName decArg) =
  case find ((== funcName) . IR.funcDeclQName) funcDecls of
    Just IR.FuncDecl { IR.funcDeclArgs = args } -> case decArg of
      Left decArgIdent ->
        case findIndex ((== decArgIdent) . IR.varPatIdent) args of
          Just decArgIndex ->
            modifyEnv $ defineDecArg funcName decArgIndex decArgIdent
          Nothing ->
            reportFatal
              $  Message srcSpan Error
              $  "The function '"
              ++ showPretty funcName
              ++ "' does not have an argument pattern '"
              ++ decArgIdent
              ++ "'."
      Right decArgPosition
        | decArgPosition > 0 && decArgPosition <= length args
        -> do
          let decArgIndex = decArgPosition - 1
              decArgIdent = IR.varPatIdent (args !! decArgIndex)
          modifyEnv $ defineDecArg funcName decArgIndex decArgIdent
        | otherwise
        -> reportFatal
          $  Message srcSpan Error
          $  "The function '"
          ++ showPretty funcName
          ++ "' does not have an argument at index "
          ++ show decArgPosition
          ++ "."
    Nothing ->
      reportFatal
        $  Message srcSpan Error
        $  "The module does not declare a function '"
        ++ showPretty funcName
        ++ "'."

-------------------------------------------------------------------------------
-- Declarations                                                              --
-------------------------------------------------------------------------------

-- | Converts the given declarations of a Haskell module.
convertDecls :: [IR.TypeDecl] -> [IR.FuncDecl] -> Converter [Coq.Sentence]
convertDecls typeDecls funcDecls = do
  typeDecls' <- convertTypeDecls typeDecls
  funcDecls' <- convertFuncDecls funcDecls
  return (typeDecls' ++ funcDecls')

-- | Converts the given data type or type synonym declarations.
convertTypeDecls :: [IR.TypeDecl] -> Converter [Coq.Sentence]
convertTypeDecls typeDecls = do
  let components = groupTypeDecls typeDecls
  concatMapM convertTypeComponent components

-------------------------------------------------------------------------------
-- Import declarations                                                       --
-------------------------------------------------------------------------------

-- | Converts the given import declarations to Coq.
convertImportDecls :: [IR.ImportDecl] -> Converter [Coq.Sentence]
convertImportDecls imports = do
  imports' <- mapM convertImportDecl imports
  return (Coq.Base.imports : imports')

-- | Convert a import declaration.
convertImportDecl :: IR.ImportDecl -> Converter Coq.Sentence
convertImportDecl (IR.ImportDecl _ modName) = do
  Just iface <- inEnv $ lookupAvailableModule modName
  generateImport (interfaceLibName iface) modName

-- | Generates a Coq import sentence for the module with the given name
--   from the given library.
--
--   Modules from the base library are imported via @From Base Require Import@
--   sentences and all other modules are also exported.
generateImport :: Coq.ModuleIdent -> IR.ModName -> Converter Coq.Sentence
generateImport libName modName = return
  (mkRequireSentence libName [Coq.ident (showPretty modName)])
 where
  -- | Makes a @From ... Require Import ...@ or  @From ... Require Export ...@.
  mkRequireSentence :: Coq.ModuleIdent -> [Coq.ModuleIdent] -> Coq.Sentence
  mkRequireSentence | libName == Coq.Base.baseLibName = Coq.requireImportFrom
                    | otherwise                       = Coq.requireExportFrom
