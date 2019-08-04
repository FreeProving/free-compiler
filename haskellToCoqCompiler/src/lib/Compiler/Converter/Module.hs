-- | This module contains functions for converting Haskell modules to Coq.

module Compiler.Converter.Module where

import           Control.Monad.Extra            ( concatMapM )
import           Data.Maybe                     ( maybe )

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyGraph
import           Compiler.Analysis.PartialityAnalysis
import           Compiler.Converter.TypeDecl
import           Compiler.Converter.QuickCheck
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Environment
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Converts a Haskell module to a Gallina module sentence and adds
--   import sentences for the Coq Base library that accompanies the compiler.
convertModuleWithPreamble :: HS.Module -> Converter [G.Sentence]
convertModuleWithPreamble ast@(HS.Module _ _ decls) = do
  mapM_ convertImportDecl decls
  coqAst <- convertModule ast
  return [CoqBase.imports, coqAst]

-- | Converts a Haskell module to a Gallina module sentence.
--
--   If no module header is present the generated module is called @"Main"@.
convertModule :: HS.Module -> Converter G.Sentence
convertModule (HS.Module _ maybeIdent decls) = do
  let ident' = G.ident (maybe "Main" id maybeIdent)
  decls' <- convertDecls decls
  return (G.LocalModuleSentence (G.LocalModule ident' decls'))

-------------------------------------------------------------------------------
-- Declarations                                                              --
-------------------------------------------------------------------------------

-- | Converts the declarations from a Haskell module to Coq.
convertDecls :: [HS.Decl] -> Converter [G.Sentence]
convertDecls decls = do
  typeDecls' <- concatMapM convertTypeComponent (groupDependencies typeGraph)
  mapM_ (modifyEnv . definePartial) (partialFunctions funcGraph)
  mapM_ filterAndDefineTypeSig      decls
  funcDecls' <- concatMapM convertFuncComponentOrQuickCheckProperty
                           (groupDependencies funcGraph)
  return (typeDecls' ++ funcDecls')
 where
  typeGraph, funcGraph :: DependencyGraph
  typeGraph = typeDependencyGraph decls
  funcGraph = funcDependencyGraph decls

-------------------------------------------------------------------------------
-- Import declarations                                                       --
-------------------------------------------------------------------------------

-- | Converts import declarations.
--
--   Currently only the import of @Test.QuickCheck@ is allowed. It enables
--   support for the translation of QuickCheck properties.
convertImportDecl :: HS.Decl -> Converter ()
convertImportDecl (HS.ImportDecl _ modIdent)
  | modIdent == "Test.QuickCheck"
  = do
    modifyEnv $ enableQuickCheck
    modifyEnv $ defineTypeCon (HS.Ident "Property") 0 (G.bare "Prop")
  | otherwise
  = reportFatal
    $ Message NoSrcSpan Error
    $ "Only the import of 'Test.QuickCheck' is supported."
convertImportDecl _ = return () -- Ignore other declarations.

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | Inserts the given type signature into the current environment.
--
--   TODO error if there are multiple type signatures for the same function.
--   TODO warn if there are unused type signatures.
filterAndDefineTypeSig :: HS.Decl -> Converter ()
filterAndDefineTypeSig (HS.TypeSig _ idents typeExpr) = mapM_
  (modifyEnv . flip defineTypeSig typeExpr . HS.Ident . HS.fromDeclIdent)
  idents
filterAndDefineTypeSig _ = return () -- ignore other declarations.
