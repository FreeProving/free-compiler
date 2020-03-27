-- | This module contains a type class for converting source spans from the
--   @haskell-src-exts@ package to the source spans of the intermediate
--   representation of the compiler.

module Compiler.Frontend.Haskell.SrcSpanConverter
  ( ConvertableSrcSpan(..)
  )
where

import           Control.Monad                  ( join )

import qualified Language.Haskell.Exts.SrcLoc  as H

import           Compiler.IR.SrcSpan

-- | Type class for @haskell-src-exts@ source spans that can be converted
--   to 'SrcSpan's for pretty printing of messages.
class ConvertableSrcSpan ss where
  -- | Converts a @haskell-src-exts@ source span to a 'SrcSpan' by
  --   attaching the corresponding line of source code.
  convertSrcSpan ::
    [(String, [String])] -- ^ A map of file names to lines of source code.
    -> ss                -- ^ The original source span to convert.
    -> SrcSpan

-- | Directly converts a 'H.SrcSpan' to a 'SrcSpan' by looking up
--   the corresponding line of code in the provided map.
instance ConvertableSrcSpan H.SrcSpan where
  convertSrcSpan codeByFilename srcSpan = SrcSpan
    { srcSpanFilename    = H.srcSpanFilename srcSpan
    , srcSpanStartLine   = H.srcSpanStartLine srcSpan
    , srcSpanStartColumn = H.srcSpanStartColumn srcSpan
    , srcSpanEndLine     = H.srcSpanEndLine srcSpan
    , srcSpanEndColumn   = H.srcSpanEndColumn srcSpan
    , srcSpanCodeLines   =
      take (H.srcSpanEndLine srcSpan - H.srcSpanStartLine srcSpan + 1)
      $ drop (H.srcSpanStartLine srcSpan - 1)
      $ maybe [] id
      $ lookup (H.srcSpanFilename srcSpan) codeByFilename
    }

-- | Converts a 'H.SrcSpanInfo' by removing additional information and applying
--   the conversion for 'H.SrcSpan's.
instance ConvertableSrcSpan H.SrcSpanInfo where
  convertSrcSpan codeByFilename = convertSrcSpan codeByFilename . H.srcInfoSpan

-- | Converts a 'H.SrcLoc' by creating a zero width source span and applying
--   the conversion for 'H.SrcSpan's.
instance ConvertableSrcSpan H.SrcLoc where
  convertSrcSpan codeByFilename =
    convertSrcSpan codeByFilename . join H.mkSrcSpan
