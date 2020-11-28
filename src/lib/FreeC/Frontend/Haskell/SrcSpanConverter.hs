{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains type class instances for converting source spans from
--   the @haskell-src-exts@ package to the source spans of the intermediate
--   representation of the compiler.
module FreeC.Frontend.Haskell.SrcSpanConverter ( ConvertibleSrcSpan(..) ) where

import           Control.Monad                ( join )
import qualified Language.Haskell.Exts.SrcLoc as HSE

import           FreeC.IR.SrcSpan

-- | Directly converts a 'HSE.SrcSpan' to a 'SrcSpan' by looking up
--   the corresponding line of code in the provided map.
instance ConvertibleSrcSpan HSE.SrcSpan where
  convertSrcSpan srcFileMap srcSpan = SrcSpan
    { srcSpanFile        = lookupSrcFile (HSE.srcSpanFilename srcSpan)
        srcFileMap
    , srcSpanStartLine   = HSE.srcSpanStartLine srcSpan
    , srcSpanStartColumn = HSE.srcSpanStartColumn srcSpan
    , srcSpanEndLine     = HSE.srcSpanEndLine srcSpan
    , srcSpanEndColumn   = HSE.srcSpanEndColumn srcSpan
    }

-- | Converts a 'HSE.SrcSpanInfo' by removing additional information and
--   applying the conversion for 'HSE.SrcSpan's.
instance ConvertibleSrcSpan HSE.SrcSpanInfo where
  convertSrcSpan srcFileMap = convertSrcSpan srcFileMap . HSE.srcInfoSpan

-- | Converts a 'HSE.SrcLoc' by creating a zero width source span and applying
--   the conversion for 'HSE.SrcSpan's.
instance ConvertibleSrcSpan HSE.SrcLoc where
  convertSrcSpan srcFileMap = convertSrcSpan srcFileMap . join HSE.mkSrcSpan
