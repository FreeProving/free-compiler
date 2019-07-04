module Compiler.Language.Coq.Preamble
  ( importDefinitions
  )
where

import qualified Data.Text                     as T

import qualified Language.Coq.Gallina          as G

import           Compiler.Util.Data.List.NonEmpty
                                                ( toNonEmptyList )
import           Compiler.Converter.Types       ( ConversionMonad(..) )

-- | Generates import sentences for the Coq libraries used by the
--   generated code.
--
--   The conversion monad is needed to import the right monad definitions.
importDefinitions :: ConversionMonad -> [G.Sentence]
importDefinitions cMonad = if cMonad == Option
  then [stringImport, libraryImport, monadImport, optionImport]
  else [stringImport, libraryImport, monadImport, identityImport]
 where
  stringImport   = requireImport [T.pack "String"]
  libraryImport  = requireImport [T.pack "ImportModules"]
  monadImport    = moduleImport [T.pack "Monad"]
  optionImport   = moduleImport [T.pack "OptionDataTypes"]
  identityImport = moduleImport [T.pack "IdentityDataTypes"]

-- | Creates a "Require Import" sentence.
requireImport :: [G.ModuleIdent] -> G.Sentence
requireImport idents =
  G.ModuleSentence (G.Require Nothing (Just G.Import) (toNonEmptyList idents))

-- | Creates a module "Import" sentence.
moduleImport :: [G.ModuleIdent] -> G.Sentence
moduleImport idents =
  G.ModuleSentence (G.ModuleImport G.Import (toNonEmptyList idents))
