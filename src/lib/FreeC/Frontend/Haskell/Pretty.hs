{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains a 'Pretty' instance for module nodes of the Haskell
--   Source Extensions AST.
--
--   The pretty instance is used to dump the output of the pattern matching
--   compiler library (See "FreeC.Frontent.Haskell.PatternMatching").

module FreeC.Frontend.Haskell.Pretty where

import qualified Language.Haskell.Exts.Pretty  as H
import qualified Language.Haskell.Exts.Syntax  as H

import           FreeC.Pretty

-- | Pretty instance for module nodes of Haskell Source Extensions AST.
instance Pretty (H.Module l) where
  pretty     = prettyString . H.prettyPrint
  prettyList = prettySeparated (line <> line)
