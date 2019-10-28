-- | This module contains functions for converting Haskell modules to Coq.

module Compiler.Converter.Module where

import           Control.Monad.Extra            ( concatMapM )
import qualified Data.Set                      as Set
import           Data.Maybe                     ( maybe )

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyGraph
import           Compiler.Analysis.PartialityAnalysis
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
  mapM_ convertImportDecl (HS.modImports ast)
  decls' <- convertDecls (HS.modTypeDecls ast)
                         (HS.modTypeSigs ast)
                         (HS.modFuncDecls ast)
  return (G.comment ("module " ++ modName) : CoqBase.imports : decls')

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

  -- Identify and remember partial functions.
  predefinedPartialFuncs <- inEnv envPartialFuncs >>= return . Set.toList
  mapM_ (modifyEnv . definePartial)
        (identifyPartialFuncs predefinedPartialFuncs dependencyGraph)

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

-- | Converts import declarations.
--
--   Currently only the import of @Test.QuickCheck@ is allowed. It enables
--   support for the translation of QuickCheck properties.
convertImportDecl :: HS.ImportDecl -> Converter ()
convertImportDecl (HS.ImportDecl srcSpan modIdent)
  | modIdent == HS.Ident "Test.QuickCheck"
  = importAndEnableQuickCheck
  | otherwise
  = reportFatal
    $ Message srcSpan Error
    $ "Only the import of 'Test.QuickCheck' is supported."

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
