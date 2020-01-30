-- | This module contains functions for converting Haskell modules to Coq.

module Compiler.Converter.Module where

import           Control.Monad                  ( when )
import           Control.Monad.Extra            ( concatMapM )
import           Data.List                      ( find
                                                , findIndex
                                                )
import qualified Data.Map                      as Map
import           Data.Maybe                     ( catMaybes )
import qualified Data.Set                      as Set

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyGraph
import           Compiler.Converter.FuncDecl
import           Compiler.Converter.QuickCheck
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
addDecArgPragma funcDecls (HS.DecArgPragma srcSpan funcIdent decArgIdent) = do
  case find ((== funcIdent) . HS.fromDeclIdent . HS.getDeclIdent) funcDecls of
    Just (HS.FuncDecl _ _ args _) -> do
      case findIndex ((== decArgIdent) . HS.fromVarPat) args of
        Just decArgIndex -> do
          let name = HS.UnQual (HS.Ident funcIdent)
          modifyEnv $ defineDecArg name decArgIndex decArgIdent
        Nothing -> do
          reportFatal
            $  Message srcSpan Error
            $  "The function "
            ++ funcIdent
            ++ " does not have an argument pattern "
            ++ decArgIdent
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
  mapM_ defineTypeSigDecl typeSigs
  funcDecls' <- convertFuncDecls funcDecls
  return (typeDecls' ++ funcDecls')

-- | Converts the given data type or type synonym declarations.
convertTypeDecls :: [HS.TypeDecl] -> Converter [G.Sentence]
convertTypeDecls typeDecls = do
  modName <- inEnv $ envModName
  let dependencyGraph = typeDependencyGraph modName typeDecls
      components      = groupDependencies dependencyGraph
  concatMapM convertTypeComponent components

-- | Converts the given function declarations.
convertFuncDecls :: [HS.FuncDecl] -> Converter [G.Sentence]
convertFuncDecls funcDecls = do
  modName <- inEnv $ envModName
  let dependencyGraph = funcDependencyGraph modName funcDecls
      components      = groupDependencies dependencyGraph

  -- Filter QuickCheck properties.
  (properties, funcComponents) <- filterQuickCheckProperties components

  -- Convert function declarations and QuickCheck properties.
  funcDecls' <- concatMapM convertFuncComponent funcComponents
  properties' <- concatMapM convertQuickCheckProperty properties
  return
    (  funcDecls'
    ++ [ G.comment "QuickCheck properties" | not (null properties') ]
    ++ properties'
    )

-------------------------------------------------------------------------------
-- Import declarations                                                       --
-------------------------------------------------------------------------------

-- | Converts the given
convertImportDecls :: [HS.ImportDecl] -> Converter [G.Sentence]
convertImportDecls imports = do
  preludeImport <- generatePreludeImport
  imports'      <- mapM convertImportDecl imports
  return (CoqBase.imports : catMaybes (preludeImport : imports'))
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
      generateImport HS.preludeModuleName

-- | Convert a import declaration.
--
--   Returns @Nothing@ if no Coq import sentence is needed (e.g., in case of
--   special imports like @Test.QuickCheck@).
convertImportDecl :: HS.ImportDecl -> Converter (Maybe G.Sentence)
convertImportDecl (HS.ImportDecl srcSpan modName) = do
  -- Enable QuickCheck.
  when (modName == quickCheckModuleName) $ modifyEnv enableQuickCheck
  -- Lookup and import module environment.
  maybeIface <- inEnv $ lookupAvailableModule modName
  case maybeIface of
    Just iface -> do
      modifyEnv $ importInterface iface
      modifyEnv $ importInterfaceAs modName iface
    Nothing ->
      reportFatal
        $  Message srcSpan Error
        $  "Could not find module '"
        ++ modName
        ++ "'"
  generateImport modName

-- | Generates a Coq import sentence for the module with the given name.
generateImport :: HS.ModName -> Converter (Maybe G.Sentence)
generateImport modName
  | modName == HS.preludeModuleName = return
  $ Just (G.requireImportFrom CoqBase.baseLibName [G.ident "Prelude"])
  | modName == quickCheckModuleName = return Nothing
  | otherwise = return $ Just (G.requireImport [G.ident (showPretty modName)])

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
    , interfaceExports = exports
    , interfaceEntries = Set.fromList entries'
    }

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | Inserts the given type signature into the current environment.
--
--   TODO error if there are multiple type signatures for the same function.
--   TODO warn if there are unused type signatures.
defineTypeSigDecl :: HS.TypeSig -> Converter ()
defineTypeSigDecl (HS.TypeSig _ idents typeSchema) = mapM_
  ( modifyEnv
  . flip defineTypeSig typeSchema
  . HS.UnQual
  . HS.Ident
  . HS.fromDeclIdent
  )
  idents
