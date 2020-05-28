{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains a 'Pretty' instance for module nodes of the Haskell
--   Source Extensions AST.
--
--   The pretty instance is used to dump the output of the pattern matching
--   compiler library (See "FreeC.Frontent.Haskell.PatternMatching").

module FreeC.Frontend.Haskell.Pretty where

import qualified Language.Haskell.Exts.Pretty  as HSE
import qualified Language.Haskell.Exts.Syntax  as HSE

import           FreeC.Pretty

-- | Pretty instance for module nodes of Haskell Source Extensions AST.
instance Pretty (HSE.Module l) where
  pretty     = prettyString . HSE.prettyPrint
  prettyList = prettySeparated (line <> line)
