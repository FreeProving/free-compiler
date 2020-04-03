{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains type class instances for converting source spans from
--   the @haskell-src-exts@ package to the source spans of the intermediate
--   representation of the compiler.

module FreeC.Frontend.Haskell.SrcSpanConverter
  ( ConvertableSrcSpan(..)
  )
where

import           Control.Monad                  ( join )

import qualified Language.Haskell.Exts.SrcLoc  as H

import           FreeC.IR.SrcSpan

-- | Directly converts a 'H.SrcSpan' to a 'SrcSpan' by looking up
--   the corresponding line of code in the provided map.
instance ConvertableSrcSpan H.SrcSpan where
  convertSrcSpan srcSpan = SrcSpan
    { srcSpanFilename    = H.srcSpanFilename srcSpan
    , srcSpanStartLine   = H.srcSpanStartLine srcSpan
    , srcSpanStartColumn = H.srcSpanStartColumn srcSpan
    , srcSpanEndLine     = H.srcSpanEndLine srcSpan
    , srcSpanEndColumn   = H.srcSpanEndColumn srcSpan
    , srcSpanCodeLines   = []
    }

-- | Converts a 'H.SrcSpanInfo' by removing additional information and applying
--   the conversion for 'H.SrcSpan's.
instance ConvertableSrcSpan H.SrcSpanInfo where
  convertSrcSpan = convertSrcSpan . H.srcInfoSpan

-- | Converts a 'H.SrcLoc' by creating a zero width source span and applying
--   the conversion for 'H.SrcSpan's.
instance ConvertableSrcSpan H.SrcLoc where
  convertSrcSpan = convertSrcSpan . join H.mkSrcSpan
