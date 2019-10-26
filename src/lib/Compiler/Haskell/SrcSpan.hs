-- | This module contains the defition of a source span data type that is used
--   by the simplified Haskell AST to store for every node the corresponding
--   portion of the source code.
--
--   Source spans can be pretty printed and are used by the error reporting
--   engine of the compiler to point the user to the relevant piece of code
--   when an error occurs.
--
--   This module also contains utility functions to work with source spans.
--   Amongst others there are functions to convert other source spans from the
--   @haskell-src-exts@ package to the data type defined in this module.

module Compiler.Haskell.SrcSpan
  ( SrcSpan(..)
  , SrcSpanConverter(..)
  , hasSourceCode
  , spansMultipleLines
  )
where

import           Control.Monad                  ( join )
import           Text.Parsec.Pos               as Parsec

import qualified Language.Haskell.Exts.SrcLoc  as H

import           Compiler.Pretty

-- | Describes the portion of the source code that caused a message to be
--   reported.
--
--   In contrast to the source spans provided by the @haskell-src-exts@ package
--   this source span provides access to the lines of code that contain the
--   source span.
data SrcSpan =
  SrcSpan
    { srcSpanFilename    :: String   -- ^ The name of the file.
    , srcSpanStartLine   :: Int      -- ^ The number of the first spanned line.
    , srcSpanStartColumn :: Int      -- ^ The offset within the first line.
    , srcSpanEndLine     :: Int      -- ^ The number of the last spanned line.
    , srcSpanEndColumn   :: Int      -- ^ The offset within the last line.
    , srcSpanCodeLines   :: [String] -- ^ The source code of the spanned lines.
    }
  | NoSrcSpan -- ^ Indicates that no location information is available.
  | FileSpan  -- ^ Points to an unknown location in the given file.
      String  -- ^ The name of the file.
  deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Source span conversion                                                    --
-------------------------------------------------------------------------------

-- | Type class for @haskell-src-exts@ source spans that can be converted
--   to 'SrcSpan's for pretty printing of messages.
class SrcSpanConverter ss where
  -- | Converts a @haskell-src-exts@ source span to a 'SrcSpan' by
  --   attaching the corresponding line of source code.
  convertSrcSpan ::
    [(String, [String])] -- ^ A map of file names to lines of source code.
    -> ss                -- ^ The original source span to convert.
    -> SrcSpan

-- | Directly converts a 'H.SrcSpan' to a 'SrcSpan' by looking up
--   the corresponding line of code in the provided map.
instance SrcSpanConverter H.SrcSpan where
  convertSrcSpan codeByFilename srcSpan = SrcSpan
    { srcSpanFilename    = H.srcSpanFilename srcSpan
    , srcSpanStartLine   = H.srcSpanStartLine srcSpan
    , srcSpanStartColumn = H.srcSpanStartColumn srcSpan
    , srcSpanEndLine     = H.srcSpanEndLine srcSpan
    , srcSpanEndColumn   = H.srcSpanEndColumn srcSpan
    , srcSpanCodeLines    =
      take (H.srcSpanEndLine srcSpan - H.srcSpanStartLine srcSpan + 1)
      $ drop (H.srcSpanStartLine srcSpan - 1)
      $ maybe [] id
      $ lookup (H.srcSpanFilename srcSpan) codeByFilename
    }

-- | Converts a 'H.SrcSpanInfo' by removing additional information and applying
--   the conversion for 'H.SrcSpan's.
instance SrcSpanConverter H.SrcSpanInfo where
  convertSrcSpan codeByFilename = convertSrcSpan codeByFilename . H.srcInfoSpan

-- | Converts a 'H.SrcLoc' by creating a zero width source span and applying
--   the conversion for 'H.SrcSpan's.
instance SrcSpanConverter H.SrcLoc where
  convertSrcSpan codeByFilename = convertSrcSpan codeByFilename . join H.mkSrcSpan

-- | Converts a Parsec 'SourcePos' to a 'SrcSpan'.
instance SrcSpanConverter Parsec.SourcePos where
  convertSrcSpan codeByFilename srcPos = SrcSpan
    { srcSpanFilename    = Parsec.sourceName srcPos
    , srcSpanStartLine   = Parsec.sourceLine srcPos
    , srcSpanStartColumn = Parsec.sourceColumn srcPos
    , srcSpanEndLine     = Parsec.sourceLine srcPos
    , srcSpanEndColumn   = Parsec.sourceColumn srcPos
    , srcSpanCodeLines   =
      return
      $ (!! Parsec.sourceLine srcPos)
      $ maybe [] id
      $ lookup (Parsec.sourceName srcPos) codeByFilename
    }

-------------------------------------------------------------------------------
-- Utility functions                                                         --
-------------------------------------------------------------------------------

-- | Tests whether the given source span has attached source code.
hasSourceCode :: SrcSpan -> Bool
hasSourceCode NoSrcSpan                          = False
hasSourceCode (FileSpan _)                       = False
hasSourceCode SrcSpan { srcSpanCodeLines = src } = not (null src)

-- | Tests whether the given source span spans multiple lines.
spansMultipleLines :: SrcSpan -> Bool
spansMultipleLines NoSrcSpan = False
spansMultipleLines (FileSpan _) = False
spansMultipleLines srcSpan = srcSpanStartLine srcSpan /= srcSpanEndLine srcSpan

-------------------------------------------------------------------------------
-- Pretty printing source spans                                              --
-------------------------------------------------------------------------------

-- | Pretty instance for a source span that displays the filename and the start
--   and end position of the source span.
--
--   If the source span spans only a single line, the end position is omitted.
instance Pretty SrcSpan where
  pretty NoSrcSpan = prettyString "<no location info>"
  pretty (FileSpan filename) = prettyString filename
  pretty srcSpan
    | spansMultipleLines srcSpan
    = prettyString (srcSpanFilename srcSpan)
      <> colon
      <> int (srcSpanStartLine srcSpan)
      <> colon
      <> int (srcSpanStartColumn srcSpan)
      <> char '-'
      <> int (srcSpanEndLine srcSpan)
      <> colon
      <> int (srcSpanEndColumn srcSpan)
    | otherwise
    = prettyString (srcSpanFilename srcSpan)
      <> colon
      <> int (srcSpanStartLine srcSpan)
      <> colon
      <> int (srcSpanStartColumn srcSpan)
