{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains a 'Pretty' instance for module nodes of the Haskell
--   Source Extensions AST.
module Compiler.Haskell.Pretty where

import qualified Language.Haskell.Exts.Pretty  as H
import qualified Language.Haskell.Exts.Syntax  as H

import           Compiler.Pretty

-- | Pretty instance for module nodes of Haskell Source Extensions AST.
instance Pretty (H.Module l) where
  pretty = prettyString . H.prettyPrint
  prettyList = prettySeparated (line <> line)
