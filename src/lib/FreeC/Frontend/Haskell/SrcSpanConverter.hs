{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains type class instances for converting source spans from
--   the @haskell-src-exts@ package to the source spans of the intermediate
--   representation of the compiler.

module FreeC.Frontend.Haskell.SrcSpanConverter
  ( ConvertableSrcSpan(..)
  )
where

import           Control.Monad                  ( join )

import qualified Language.Haskell.Exts.SrcLoc  as HSE

import           FreeC.IR.SrcSpan

-- | Directly converts a 'HSE.SrcSpan' to a 'SrcSpan' by looking up
--   the corresponding line of code in the provided map.
instance ConvertableSrcSpan HSE.SrcSpan where
  convertSrcSpan srcSpan = SrcSpan
    { srcSpanFilename    = HSE.srcSpanFilename srcSpan
    , srcSpanStartLine   = HSE.srcSpanStartLine srcSpan
    , srcSpanStartColumn = HSE.srcSpanStartColumn srcSpan
    , srcSpanEndLine     = HSE.srcSpanEndLine srcSpan
    , srcSpanEndColumn   = HSE.srcSpanEndColumn srcSpan
    , srcSpanCodeLines   = []
    }

-- | Converts a 'HSE.SrcSpanInfo' by removing additional information and applying
--   the conversion for 'HSE.SrcSpan's.
instance ConvertableSrcSpan HSE.SrcSpanInfo where
  convertSrcSpan = convertSrcSpan . HSE.srcInfoSpan

-- | Converts a 'HSE.SrcLoc' by creating a zero width source span and applying
--   the conversion for 'HSE.SrcSpan's.
instance ConvertableSrcSpan HSE.SrcLoc where
  convertSrcSpan = convertSrcSpan . join HSE.mkSrcSpan
