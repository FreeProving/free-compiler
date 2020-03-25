-- | This module contains functions for converting Haskell modules to Coq.

module Compiler.Converter.Module where

import           Control.Monad                  ( (>=>) )
import           Control.Monad.Extra            ( concatMapM )
import           Data.List                      ( find
                                                , findIndex
                                                )
import qualified Data.Map                      as Map
import qualified Data.Set                      as Set

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyGraph
import           Compiler.Converter.FuncDecl
import           Compiler.Converter.TypeDecl
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.Resolver
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pipeline
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Converts a Haskell module to a Gallina sentences.
convertModule :: HS.Module -> Converter [G.Sentence]
convertModule = moduleEnv . (runPipeline >=> convertModule')

-- | Like 'convertModule'' but does not apply any compiler passes beforehand.
convertModule' :: HS.Module -> Converter ([G.Sentence], ModuleInterface)
convertModule' haskellAst = do
  -- Convert module contents.
  imports' <- convertImportDecls (HS.modImports haskellAst)
  mapM_ (addDecArgPragma (HS.modFuncDecls haskellAst))
        (HS.modPragmas haskellAst)
  decls' <- convertDecls (HS.modTypeDecls haskellAst)
                         (HS.modFuncDecls haskellAst)
  -- Export module interface.
  let coqAst =
        G.comment ("module " ++ HS.modName haskellAst) : imports' ++ decls'
  interface <- exportInterface (HS.modName haskellAst)
  return (coqAst, interface)

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
addDecArgPragma :: [HS.FuncDecl] -> HS.Pragma -> Converter ()
addDecArgPragma funcDecls (HS.DecArgPragma srcSpan funcName decArg) = do
  case find ((== funcName) . HS.funcDeclQName) funcDecls of
    Just (HS.FuncDecl { HS.funcDeclArgs = args }) -> case decArg of
      Left decArgIdent ->
        case findIndex ((== decArgIdent) . HS.varPatIdent) args of
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
              decArgIdent = HS.varPatIdent (args !! decArgIndex)
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
convertDecls :: [HS.TypeDecl] -> [HS.FuncDecl] -> Converter [G.Sentence]
convertDecls typeDecls funcDecls = do
  typeDecls' <- convertTypeDecls typeDecls
  funcDecls' <- convertFuncDecls funcDecls
  return (typeDecls' ++ funcDecls')

-- | Converts the given data type or type synonym declarations.
convertTypeDecls :: [HS.TypeDecl] -> Converter [G.Sentence]
convertTypeDecls typeDecls = do
  let dependencyGraph = typeDependencyGraph typeDecls
      components      = groupDependencies dependencyGraph
  concatMapM convertTypeComponent components

-------------------------------------------------------------------------------
-- Import declarations                                                       --
-------------------------------------------------------------------------------

-- | Converts the given import declarations to Coq.
convertImportDecls :: [HS.ImportDecl] -> Converter [G.Sentence]
convertImportDecls imports = do
  imports' <- mapM convertImportDecl imports
  return (CoqBase.imports : imports')

-- | Convert a import declaration.
convertImportDecl :: HS.ImportDecl -> Converter G.Sentence
convertImportDecl (HS.ImportDecl _ modName) = do
  Just iface <- inEnv $ lookupAvailableModule modName
  generateImport (interfaceLibName iface) modName

-- | Generates a Coq import sentence for the module with the given name
--   from the given library.
--
--   Modules from the base library are imported via @From Base Require Import@
--   sentences and all other modules are also exported.
generateImport :: G.ModuleIdent -> HS.ModName -> Converter G.Sentence
generateImport libName modName = return
  (mkRequireSentence libName [G.ident (showPretty modName)])
 where
  -- | Makes a @From ... Require Import ...@ or  @From ... Require Export ...@.
  mkRequireSentence :: G.ModuleIdent -> [G.ModuleIdent] -> G.Sentence
  mkRequireSentence | libName == CoqBase.baseLibName = G.requireImportFrom
                    | otherwise                      = G.requireExportFrom

-------------------------------------------------------------------------------
-- Exports                                                                   --
-------------------------------------------------------------------------------

-- | Generates the module interface exported by the currently translated module.
--
--   The interface contains all (non-internal) top-level entries that are
--   currently in the environment. Only entries that are defined in the
--   currently translated module are listed as exported. All other entries
--   are "hidden". Hidden entries are included such that module interfaces
--   are self contained and type synonyms can be expanded properly.
--   All references in the entries are converted to fully qualified
--   identifiers before they are exported.
exportInterface :: HS.ModName -> Converter ModuleInterface
exportInterface modName = do
  exports <-
    inEnv
    $ filter (isExported . snd)
    . map entryScopedName
    . Map.elems
    . envEntries
  entries <-
    inEnv
    $ filter (not . HS.isInternalQName . entryName)
    . Map.elems
    . envEntries
  entries' <- mapM resolveReferences entries
  return ModuleInterface { interfaceModName = modName
                         , interfaceLibName = CoqBase.generatedLibName
                         , interfaceExports = Set.fromList exports
                         , interfaceEntries = Set.fromList entries'
                         }
 where
   -- Tests whether to export the entry with the given name.
   --
   -- Only non-internal entries that are defined at top-level of the exported
   -- module are exported.
  isExported :: HS.QName -> Bool
  isExported (HS.Qual modName' name) =
    modName' == modName && not (HS.isInternalName name)
  isExported (HS.UnQual _) = False
