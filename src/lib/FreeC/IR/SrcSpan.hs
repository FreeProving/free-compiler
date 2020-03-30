-- | This module contains the definition of a source span data type that is
--   used by the AST of the intermediate language to store for every node the
--   corresponding portion of the source code.
--
--   Source spans can be pretty printed and are used by the error reporting
--   engine of the compiler to point the user to the relevant piece of code
--   when an error occurs.

module FreeC.IR.SrcSpan
  ( SrcSpan(..)
    -- * Predicates
  , hasSrcSpanFilename
  , hasSourceCode
  , spansMultipleLines
  )
where

import           FreeC.Pretty

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
      { srcSpanFilename :: String    -- ^ The name of the file.
      }
  deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Predicates                                                                --
-------------------------------------------------------------------------------

-- | Tests whether the given 'SrcSpan' contains filename information (i.e.,
--   there is a field `srcSpanFilename`).
hasSrcSpanFilename :: SrcSpan -> Bool
hasSrcSpanFilename NoSrcSpan = False
hasSrcSpanFilename _         = True

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
  pretty NoSrcSpan           = prettyString "<no location info>"
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
