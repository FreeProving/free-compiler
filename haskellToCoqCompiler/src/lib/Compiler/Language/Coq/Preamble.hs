module Compiler.Language.Coq.Preamble
  ( importDefinitions
  )
where

import qualified Data.Text                     as T

import qualified Language.Coq.Gallina          as G

import           Compiler.Util.Data.List.NonEmpty
                                                ( toNonEmptyList )

-- | Generates import sentences for the Coq libraries used by the
--   generated code.
--
--   The conversion monad is needed to import the right monad definitions.
importDefinitions :: [G.Sentence]
importDefinitions = [stringImport, libraryImport, monadImport]
 where
  stringImport   = requireImport [T.pack "String"]
  libraryImport  = requireImport [T.pack "ImportModules"]
  monadImport    = moduleImport [T.pack "Monad"]

-- | Creates a "Require Import" sentence.
requireImport :: [G.ModuleIdent] -> G.Sentence
requireImport idents =
  G.ModuleSentence (G.Require Nothing (Just G.Import) (toNonEmptyList idents))

-- | Creates a module "Import" sentence.
moduleImport :: [G.ModuleIdent] -> G.Sentence
moduleImport idents =
  G.ModuleSentence (G.ModuleImport G.Import (toNonEmptyList idents))
