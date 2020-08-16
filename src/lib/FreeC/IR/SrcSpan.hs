-- | This module contains the definition of a source span data type that is
--   used by the AST of the intermediate language to store for every node the
--   corresponding portion of the source code.
--
--   Source spans can be pretty printed and are used by the error reporting
--   engine of the compiler to point the user to the relevant piece of code
--   when an error occurs.
module FreeC.IR.SrcSpan
  ( -- * Source Files
    SrcFile(..)
  , SrcFileMap
  , mkSrcFile
  , mkSrcFileMap
    -- * Source Spans
  , SrcSpan(..)
    -- * Predicates
  , hasSrcSpanFilename
  , hasSourceCode
  , spansMultipleLines
    -- * Conversion
  , ConvertibleSrcSpan(..)
  , convertSrcSpanWithCode
  , addSourceCode
  ) where

import           Data.Tuple.Extra ( (&&&) )

import           FreeC.Pretty

-- | Data type that contains the name and contents of source files.
--
--   The contents of the source file are stored as a string for parsing
--   and as a list of lines for error messages (i.e., to construct 'SrcSpan's).
data SrcFile = SrcFile
  { srcFileName     :: FilePath -- ^ The name of the file.
  , srcFileContents :: String   -- ^ The contents of the file.
  , srcFileLines    :: [ String ] -- ^ The lines of 'srcFileContents'.
  }

-- | Type for a map that associates source files with their filename.
type SrcFileMap = [ (FilePath, SrcFile) ]

-- | Smart constructor for 'SrcFile' that automatically splits the file
--   contents into lines.
mkSrcFile :: FilePath -> String -> SrcFile
mkSrcFile filename contents = SrcFile
  { srcFileName     = filename
  , srcFileContents = contents
  , srcFileLines    = lines contents
  }

-- | Smart constructor for 'SrcFileMap' for the given 'SrcFile's.
mkSrcFileMap :: [ SrcFile ] -> SrcFileMap
mkSrcFileMap = map (srcFileName &&& id)

-- | Looks up a 'SrcFile' in a 'SrcFileMap'.
lookupSrcFile :: FilePath -> SrcFileMap -> Maybe SrcFile
lookupSrcFile = lookup

-------------------------------------------------------------------------------
-- Source Spans                                                              --
-------------------------------------------------------------------------------
-- | Describes the portion of the source code that caused a message to be
--   reported.
--
--   In contrast to the source spans provided by the @haskell-src-exts@ package
--   this source span provides access to the lines of code that contain the
--   source span.
data SrcSpan
  = SrcSpan
      { srcSpanFilename    :: String   -- ^ The name of the file.
      , srcSpanStartLine   :: Int      -- ^ The number of the first spanned line.
      , srcSpanStartColumn :: Int      -- ^ The offset within the first line.
      , srcSpanEndLine     :: Int      -- ^ The number of the last spanned line.
      , srcSpanEndColumn   :: Int      -- ^ The offset within the last line.
      , srcSpanCodeLines   :: [ String ] -- ^ The source code of the spanned lines.
      }
  | NoSrcSpan -- ^ Indicates that no location information is available.
  | FileSpan  -- ^ Points to an unknown location in the given file.
      { srcSpanFilename :: String    -- ^ The name of the file.
      }
 deriving ( Eq, Show )

-------------------------------------------------------------------------------
-- Predicates                                                                --
-------------------------------------------------------------------------------
-- | Tests whether the given 'SrcSpan' contains filename information (i.e.,
--   there is a field 'srcSpanFilename').
hasSrcSpanFilename :: SrcSpan -> Bool
hasSrcSpanFilename NoSrcSpan = False
hasSrcSpanFilename _         = True

-- | Tests whether the given source span has attached source code.
hasSourceCode :: SrcSpan -> Bool
hasSourceCode NoSrcSpan = False
hasSourceCode (FileSpan _) = False
hasSourceCode SrcSpan { srcSpanCodeLines = src } = not (null src)

-- | Tests whether the given source span spans multiple lines.
spansMultipleLines :: SrcSpan -> Bool
spansMultipleLines NoSrcSpan    = False
spansMultipleLines (FileSpan _) = False
spansMultipleLines srcSpan
  = srcSpanStartLine srcSpan /= srcSpanEndLine srcSpan

-------------------------------------------------------------------------------
-- Conversion                                                                --
-------------------------------------------------------------------------------
-- | Type class for source spans from other packages that can be converted
--   to 'SrcSpan's for pretty printing of messages.
class ConvertibleSrcSpan ss where
  -- | Converts the given third party source span to a 'SrcSpan' by attaching
  --   the corresponding line of source code.
  convertSrcSpan :: ss -> SrcSpan

-- | Like 'convertSrcSpan' but also adds source code using 'addSourceCode'.
convertSrcSpanWithCode :: ConvertibleSrcSpan ss => SrcFileMap -> ss -> SrcSpan
convertSrcSpanWithCode srcFiles = addSourceCode srcFiles . convertSrcSpan

-- | Adds source code to the given source span if it does not have source code
--   already.
addSourceCode :: SrcFileMap -> SrcSpan -> SrcSpan
addSourceCode srcFiles srcSpan@SrcSpan { srcSpanCodeLines = [] } = srcSpan
  { srcSpanCodeLines = take
      (srcSpanEndLine srcSpan - srcSpanStartLine srcSpan + 1)
      $ drop (srcSpanStartLine srcSpan - 1)
      $ maybe [] srcFileLines
      $ lookupSrcFile (srcSpanFilename srcSpan) srcFiles
  }
addSourceCode _ srcSpan = srcSpan

-------------------------------------------------------------------------------
-- Pretty Printing Source Spans                                              --
-------------------------------------------------------------------------------
-- | Pretty instance for a source span that displays the filename and the start
--   and end position of the source span.
--
--   If the source span spans only a single line, the end position is omitted.
instance Pretty SrcSpan where
  pretty NoSrcSpan = prettyString "<no location info>"
  pretty (FileSpan filename) = prettyString filename
  pretty srcSpan
    | spansMultipleLines srcSpan = prettyString (srcSpanFilename srcSpan)
      <> colon
      <> int (srcSpanStartLine srcSpan)
      <> colon
      <> int (srcSpanStartColumn srcSpan)
      <> char '-'
      <> int (srcSpanEndLine srcSpan)
      <> colon
      <> int (srcSpanEndColumn srcSpan)
    | otherwise = prettyString (srcSpanFilename srcSpan)
      <> colon
      <> int (srcSpanStartLine srcSpan)
      <> colon
      <> int (srcSpanStartColumn srcSpan)
