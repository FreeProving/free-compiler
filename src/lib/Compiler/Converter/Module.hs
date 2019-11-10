-- | This module contains functions for converting Haskell modules to Coq.

module Compiler.Converter.Module where

import           Control.Monad                  ( when )
import           Control.Monad.Extra            ( concatMapM )
import qualified Data.Map                      as Map
import           Data.Maybe                     ( maybeToList )
import qualified Data.Set                      as Set

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyGraph
import           Compiler.Converter.FuncDecl
import           Compiler.Converter.TypeDecl
import           Compiler.Converter.QuickCheck
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Environment
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
  decls'   <- convertDecls (HS.modTypeDecls haskellAst)
                           (HS.modTypeSigs haskellAst)
                           (HS.modFuncDecls haskellAst)
  -- Export module interface.
  let coqAst = G.comment ("module " ++ modName) : imports' ++ decls'
  interface <- exportInterface
  return (coqAst, interface)


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
      Just <$> generateImport HS.preludeModuleName

-- | Convert a import declaration.
--
--   Returns @Nothing@ if no Coq import sentence is needed (e.g., in case of
--   special imports like @Test.QuickCheck@).
convertImportDecl :: HS.ImportDecl -> Converter (G.Sentence)
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
generateImport :: HS.ModName -> Converter G.Sentence
generateImport modName
  | modName == HS.preludeModuleName = return
  $ G.requireImportFrom CoqBase.baseLibName [G.ident "Prelude"]
  | otherwise = return $ G.requireImport [G.ident (showPretty modName)] -- TODO rename module?

-------------------------------------------------------------------------------
-- Exports                                                                   --
-------------------------------------------------------------------------------

-- | Generates the module interface exported by the currently translated module.
exportInterface :: Converter ModuleInterface
exportInterface = do
  env <- getEnv
  return $ ModuleInterface
    { interfaceModName = envModName env
    , interfaceEntries = Set.unions
      $ Map.elems
      $ Map.map fst
      $ Map.filter ((== 0) . snd)
      $ envEntries env
    }

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | Inserts the given type signature into the current environment.
--
--   TODO error if there are multiple type signatures for the same function.
--   TODO warn if there are unused type signatures.
defineTypeSigDecl :: HS.TypeSig -> Converter ()
defineTypeSigDecl (HS.TypeSig _ idents typeExpr) = mapM_
  ( modifyEnv
  . flip defineTypeSig typeExpr
  . HS.UnQual
  . HS.Ident
  . HS.fromDeclIdent
  )
  idents
