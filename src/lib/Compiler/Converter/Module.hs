-- | This module contains functions for converting Haskell modules to Coq.

module Compiler.Converter.Module where

import           Control.Monad.Extra            ( concatMapM )
import           Data.Maybe                     ( catMaybes
                                                , maybe
                                                )

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
--
--   If no module header is present the generated module is called @"Main"@.
convertModule :: HS.Module -> Converter [G.Sentence]
convertModule ast = do
  let modName = maybe "Main" showPretty $ HS.modName ast
  imports' <- convertImportDecls (HS.modImports ast)
  decls'   <- convertDecls (HS.modTypeDecls ast)
                           (HS.modTypeSigs ast)
                           (HS.modFuncDecls ast)
  return (G.comment ("module " ++ modName) : imports' ++ decls')

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
  let dependencyGraph = typeDependencyGraph typeDecls
      components      = groupDependencies dependencyGraph
  concatMapM convertTypeComponent components

-- | Converts the given function declarations.
convertFuncDecls :: [HS.FuncDecl] -> Converter [G.Sentence]
convertFuncDecls funcDecls = do
  let dependencyGraph = funcDependencyGraph funcDecls
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
      Just preludeEnv <- inEnv $ lookupAvailableModule HS.preludeModuleName
      modifyEnv $ importEnv preludeEnv
      Just <$> generateImport HS.preludeModuleName

-- | Convert a import declaration.
--
--   Returns @Nothing@ if no Coq import sentence is needed (e.g., in case of
--   special imports like @Test.QuickCheck@).
convertImportDecl :: HS.ImportDecl -> Converter (Maybe G.Sentence)
convertImportDecl (HS.ImportDecl _ (HS.Ident "Test.QuickCheck")) = do
  importAndEnableQuickCheck
  return Nothing
convertImportDecl (HS.ImportDecl srcSpan modName) = do
  maybeModEnv <- inEnv $ lookupAvailableModule modName
  case maybeModEnv of
    Just modEnv -> modifyEnv $ importEnv modEnv
    Nothing ->
      reportFatal
        $  Message srcSpan Error
        $  "Could not find module '"
        ++ showPretty modName
        ++ "'"
  Just <$> generateImport modName

-- | Generates a Coq import sentence for the module with the given name.
generateImport :: HS.Name -> Converter G.Sentence
generateImport modName
  | modName == HS.preludeModuleName = return
  $ G.requireImportFrom CoqBase.baseLibName [G.ident "Prelude"]
  | otherwise = return $ G.requireImport [G.ident (showPretty modName)] -- TODO rename module?

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | Inserts the given type signature into the current environment.
--
--   TODO error if there are multiple type signatures for the same function.
--   TODO warn if there are unused type signatures.
defineTypeSigDecl :: HS.TypeSig -> Converter ()
defineTypeSigDecl (HS.TypeSig _ idents typeExpr) = mapM_
  (modifyEnv . flip defineTypeSig typeExpr . HS.Ident . HS.fromDeclIdent)
  idents
