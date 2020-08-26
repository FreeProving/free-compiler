-- | This module contains functions for converting Haskell modules to Coq.
module FreeC.Backend.Coq.Converter.Module where

import           Control.Monad.Extra                  ( concatMapM )
import           Data.List.Extra                      ( concatUnzip )
import           Data.List.NonEmpty                   ( NonEmpty(..) )
import           Data.Maybe                           ( catMaybes )
import qualified Data.Text                            as Text

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
  (sentences, qualNotations)
    <- concatUnzip <$> mapM convertTypeComponent components
  let 
    -- Put qualified notations into a single submodule
    qualNotModule       = Coq.LocalModuleSentence
      $ Coq.LocalModule Coq.Base.qualifiedNotation qualNotations
    qualNotModuleExport = Coq.ModuleSentence
      $ Coq.ModuleImport Coq.Export
      $ Coq.Base.qualifiedNotation :| []
  return
    $ sentences
    ++ [ Coq.comment "Qualified smart constructors"
       , qualNotModule
       , qualNotModuleExport
       ]

-------------------------------------------------------------------------------
-- Import Declarations                                                       --
-------------------------------------------------------------------------------
-- | Converts the given import declarations to Coq.
convertImportDecls :: [IR.ImportDecl] -> Converter [Coq.Sentence]
convertImportDecls imports = do
  imports' <- concatMapM convertImportDecl imports
  return (Coq.Base.imports : imports')

-- | Convert an import declaration.
convertImportDecl :: IR.ImportDecl -> Converter [Coq.Sentence]
convertImportDecl (IR.ImportDecl _ modName) = do
  Just iface <- inEnv $ lookupAvailableModule modName
  imports <- generateImport (interfaceLibName iface) modName
  notationImports <- generateNotationImport (interfaceLibName iface) modName
  return $ imports : (catMaybes [notationImports])

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
  mkRequireSentence | libName == Coq.Base.baseLibName = Coq.requireImportFrom
                    | otherwise = Coq.requireFrom

-- | Generates a Coq import sentence for the submodule of the module with the
--   given name that contains qualified notations.
--
--   Modules from the base library do not contain such a module and are skipped.
generateNotationImport
  :: Coq.ModuleIdent -> IR.ModName -> Converter (Maybe Coq.Sentence)
generateNotationImport libName modName
  | libName == Coq.Base.baseLibName = return Nothing
  | otherwise = return $ Just (Coq.importFrom [Text.append libName accessor])
 where
  accessor = Text.cons '.'
    $ Text.append (Coq.ident (showPretty modName))
    $ Text.cons '.' Coq.Base.qualifiedNotation
