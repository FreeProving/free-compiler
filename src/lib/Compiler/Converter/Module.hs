-- | This module contains functions for converting Haskell modules to Coq.

module Compiler.Converter.Module where

import           Control.Monad.Extra            ( concatMapM )
import           Data.List                      ( find
                                                , findIndex
                                                )
import qualified Data.Map                      as Map
import           Data.Maybe                     ( maybeToList )
import qualified Data.Set                      as Set

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyGraph
import           Compiler.Analysis.TypeInference
import           Compiler.Converter.FuncDecl
import           Compiler.Converter.TypeDecl
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.Importer
import           Compiler.Environment.Resolver
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Converts a Haskell module to a Gallina sentences.
convertModule :: HS.Module -> Converter [G.Sentence]
convertModule haskellAst = moduleEnv $ do
  -- Remember name of converted module.
  let modName = HS.modName haskellAst
  modifyEnv $ \env -> env { envModName = modName }
  -- Convert module contents.
  imports' <- convertImportDecls (HS.modImports haskellAst)
  mapM_ (addDecArgPragma (HS.modFuncDecls haskellAst))
        (HS.modPragmas haskellAst)
  decls' <- convertDecls (HS.modTypeDecls haskellAst)
                         (HS.modTypeSigs haskellAst)
                         (HS.modFuncDecls haskellAst)
  -- Export module interface.
  let coqAst = G.comment ("module " ++ modName) : imports' ++ decls'
  interface <- exportInterface
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
addDecArgPragma funcDecls (HS.DecArgPragma srcSpan funcIdent decArg) = do
  let funName = HS.UnQual (HS.Ident funcIdent)
  case find ((== funcIdent) . HS.fromDeclIdent . HS.getDeclIdent) funcDecls of
    Just (HS.FuncDecl { HS.funcDeclArgs = args }) -> case decArg of
      Left decArgIdent ->
        case findIndex ((== decArgIdent) . HS.fromVarPat) args of
          Just decArgIndex ->
            modifyEnv $ defineDecArg funName decArgIndex decArgIdent
          Nothing ->
            reportFatal
              $  Message srcSpan Error
              $  "The function "
              ++ funcIdent
              ++ " does not have an argument pattern "
              ++ decArgIdent
              ++ "."
      Right decArgPosition
        | decArgPosition > 0 && decArgPosition <= length args
        -> do
          let decArgIndex = decArgPosition - 1
              decArgIdent = HS.fromVarPat (args !! decArgIndex)
          modifyEnv $ defineDecArg funName decArgIndex decArgIdent
        | otherwise
        -> reportFatal
          $  Message srcSpan Error
          $  "The function "
          ++ funcIdent
          ++ " does not have an argument at index "
          ++ show decArgPosition
          ++ "."
    Nothing -> do
      modName <- inEnv envModName
      reportFatal
        $  Message srcSpan Error
        $  "The module "
        ++ modName
        ++ " does not declare a function "
        ++ funcIdent
        ++ "."

-------------------------------------------------------------------------------
-- Declarations                                                              --
-------------------------------------------------------------------------------

-- | Converts the given declarations of a Haskell module.
convertDecls
  :: [HS.TypeDecl] -> [HS.TypeSig] -> [HS.FuncDecl] -> Converter [G.Sentence]
convertDecls typeDecls typeSigs funcDecls = do
  typeDecls' <- convertTypeDecls typeDecls
  funcDecls' <- addTypeSigsToFuncDecls typeSigs funcDecls >>= convertFuncDecls
  return (typeDecls' ++ funcDecls')

-- | Converts the given data type or type synonym declarations.
convertTypeDecls :: [HS.TypeDecl] -> Converter [G.Sentence]
convertTypeDecls typeDecls = do
  modName <- inEnv $ envModName
  let dependencyGraph = typeDependencyGraph modName typeDecls
      components      = groupDependencies dependencyGraph
  concatMapM convertTypeComponent components

-------------------------------------------------------------------------------
-- Import declarations                                                       --
-------------------------------------------------------------------------------

-- | Converts the given
convertImportDecls :: [HS.ImportDecl] -> Converter [G.Sentence]
convertImportDecls imports = do
  preludeImport <- generatePreludeImport
  imports'      <- mapM convertImportDecl imports
  return (CoqBase.imports : maybeToList preludeImport ++ imports')
 where
  -- | Tests whether there is an explicit import for the @Prelude@ module.
  importsPrelude :: Bool
  importsPrelude = elem HS.preludeModuleName (map HS.importName imports)

  -- | Imports the @Prelude@ module implicitly.
  generatePreludeImport :: Converter (Maybe G.Sentence)
  generatePreludeImport
    | importsPrelude = return Nothing
    | otherwise = do
      Just preludeIface <- inEnv $ lookupAvailableModule HS.preludeModuleName
      modifyEnv $ importInterface preludeIface
      modifyEnv $ importInterfaceAs HS.preludeModuleName preludeIface
      Just
        <$> generateImport (interfaceLibName preludeIface) HS.preludeModuleName

-- | Convert a import declaration.
convertImportDecl :: HS.ImportDecl -> Converter G.Sentence
convertImportDecl (HS.ImportDecl srcSpan modName) = do
  -- Lookup and import module environment.
  maybeIface <- inEnv $ lookupAvailableModule modName
  case maybeIface of
    Just iface -> do
      modifyEnv $ importInterface iface
      modifyEnv $ importInterfaceAs modName iface
      generateImport (interfaceLibName iface) modName
    Nothing ->
      reportFatal
        $  Message srcSpan Error
        $  "Could not find module '"
        ++ modName
        ++ "'"

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
exportInterface :: Converter ModuleInterface
exportInterface = do
  modName <- inEnv envModName
  exports <-
    inEnv
    $ Set.filter (not . HS.isInternalQName . snd)
    . Set.unions
    . map (Set.map entryScopedName . fst)
    . filter ((== 0) . snd)
    . Map.elems
    . envEntries
  entries <-
    inEnv
    $ filter (not . HS.isInternalQName . entryName)
    . Set.toList
    . Set.unions
    . map fst
    . Map.elems
    . envEntries
  entries' <- mapM resolveReferences entries
  return ModuleInterface
    { interfaceModName = modName
    , interfaceLibName = CoqBase.generatedLibName
    , interfaceExports = exports
    , interfaceEntries = Set.fromList entries'
    }
