-- | This module contains functions for converting Haskell modules to Coq.
module FreeC.Backend.Coq.Converter.Module where

import           Control.Monad.Extra                  ( concatMapM )

import qualified FreeC.Backend.Coq.Base               as Coq.Base
import           FreeC.Backend.Coq.Converter.FuncDecl
import           FreeC.Backend.Coq.Converter.TypeDecl
import qualified FreeC.Backend.Coq.Syntax             as Coq
import           FreeC.Environment
import           FreeC.Environment.ModuleInterface
import           FreeC.IR.DependencyGraph
import           FreeC.IR.Pragma
import qualified FreeC.IR.Syntax                      as IR
import           FreeC.Monad.Converter
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------
-- | Converts an IR module to Gallina sentences.
convertModule :: IR.Module -> Converter [Coq.Sentence]
convertModule haskellAst = do
  imports' <- convertImportDecls (IR.modImports haskellAst)
  mapM_ (addDecArgPragma (IR.modFuncDecls haskellAst))
    (IR.modPragmas haskellAst)
  decls' <- convertDecls (IR.modTypeDecls haskellAst)
    (IR.modFuncDecls haskellAst)
  return (Coq.comment ("module " ++ IR.modName haskellAst) : imports' ++ decls')

-------------------------------------------------------------------------------
-- Declarations                                                              --
-------------------------------------------------------------------------------
-- | Converts the given declarations of an IR module.
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
-- Import Declarations                                                       --
-------------------------------------------------------------------------------
-- | Converts the given import declarations to Coq.
convertImportDecls :: [IR.ImportDecl] -> Converter [Coq.Sentence]
convertImportDecls imports = do
  imports' <- mapM convertImportDecl imports
  return (Coq.Base.imports : imports')

-- | Convert an import declaration.
convertImportDecl :: IR.ImportDecl -> Converter Coq.Sentence
convertImportDecl (IR.ImportDecl _ modName) = do
  Just iface <- inEnv $ lookupAvailableModule modName
  generateImport (interfaceLibName iface) modName

-- | Generates a Coq import sentence for the module with the given name
--   from the given library.
--
--   Modules from the base library are imported via @From Base Require Import@
--   sentences. Other external modules are imported via @From … Require@
--   sentences, which means that references to these modules' contents must
--   be qualified in the code.
generateImport :: Coq.ModuleIdent -> IR.ModName -> Converter Coq.Sentence
generateImport libName modName = return
  (mkRequireSentence libName [Coq.ident (showPretty modName)])
 where
  -- | Makes a @From … Require Import …@ or  @From … Require …@.
  mkRequireSentence :: Coq.ModuleIdent -> [Coq.ModuleIdent] -> Coq.Sentence
  mkRequireSentence
    | libName == Coq.Base.baseLibName = Coq.requireImportFrom
    | otherwise = Coq.requireFrom
