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
  , mkSrcFile
  , hasSrcFileContents
    -- * Source File Maps
  , SrcFileMap
  , mkSrcFileMap
  , lookupSrcFile
    -- * Source Spans
  , SrcSpan(..)
    -- * Selectors
  , srcSpanCodeLines
    -- * Predicates
  , hasSrcSpanFile
  , hasSourceCode
  , spansMultipleLines
    -- * Conversion
  , ConvertibleSrcSpan(..)
  ) where

import           Data.Maybe       ( fromMaybe )
import           Data.Tuple.Extra ( (&&&) )

import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Source Files                                                              --
-------------------------------------------------------------------------------
-- | Data type that contains the name and contents of source files.
--
--   The contents of the source file are stored as a string for parsing
--   and as a list of lines for error messages.
data SrcFile
  = SrcFile { srcFileName     :: FilePath -- ^ The name of the file.
            , srcFileContents :: String   -- ^ The contents of the file.
            , srcFileLines    :: [String] -- ^ The lines of 'srcFileContents'.
            }
  | NoSrcFile -- ^ A source file whose contents are unknown.
      { srcFileName :: FilePath
      }
 deriving ( Eq, Show )

-- | Smart constructor for 'SrcFile' that automatically splits the file
--   contents into lines.
mkSrcFile :: FilePath -> String -> SrcFile
mkSrcFile filename contents = SrcFile
  { srcFileName     = filename
  , srcFileContents = contents
  , srcFileLines    = lines contents
  }

-- | Tests whether the contents of the given source file are known.
hasSrcFileContents :: SrcFile -> Bool
hasSrcFileContents SrcFile {}   = True
hasSrcFileContents NoSrcFile {} = False

-------------------------------------------------------------------------------
-- Source File Maps                                                          --
-------------------------------------------------------------------------------
-- | Type for a map that associates source files with their filename.
type SrcFileMap = [(FilePath, SrcFile)]

-- | Smart constructor for 'SrcFileMap' for the given 'SrcFile's.
mkSrcFileMap :: [SrcFile] -> SrcFileMap
mkSrcFileMap = map (srcFileName &&& id)

-- | Looks up a 'SrcFile' in a 'SrcFileMap'.
--
--   Returns 'NoSrcFile' if the map does not contain such a source file.
lookupSrcFile :: FilePath -> SrcFileMap -> SrcFile
lookupSrcFile filename = fromMaybe (NoSrcFile filename) . lookup filename

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
      { srcSpanFile        :: SrcFile -- ^ The source file if known.
      , srcSpanStartLine   :: Int     -- ^ The number of the first line.
      , srcSpanStartColumn :: Int     -- ^ The offset within the first line.
      , srcSpanEndLine     :: Int     -- ^ The number of the last line.
      , srcSpanEndColumn   :: Int     -- ^ The offset within the last line.
      }
  | NoSrcSpan -- ^ Indicates that no location information is available.
  | FileSpan  -- ^ Points to an unknown location in the given file.
      { srcSpanFile :: SrcFile -- ^ The name of the file.
      }
 deriving ( Eq, Show )

-------------------------------------------------------------------------------
-- Selectors                                                                 --
-------------------------------------------------------------------------------
-- | Gets the lines of source code spanned by the given source span.
--
--   Returns an empty list if the given source span does not satisfy the
--   'hasSourceCode' predicate.
srcSpanCodeLines :: SrcSpan -> [String]
srcSpanCodeLines NoSrcSpan          = []
srcSpanCodeLines (FileSpan _)       = []
srcSpanCodeLines srcSpan@SrcSpan {}
  | hasSrcFileContents (srcSpanFile srcSpan) = take
    (srcSpanEndLine srcSpan - srcSpanStartLine srcSpan + 1)
    $ drop (srcSpanStartLine srcSpan - 1)
    $ srcFileLines (srcSpanFile srcSpan)
  | otherwise = []

-------------------------------------------------------------------------------
-- Predicates                                                                --
-------------------------------------------------------------------------------
-- | Tests whether the given 'SrcSpan' contains information about the file
--   that is spanned (i.e., there is a field 'srcSpanFile').
hasSrcSpanFile :: SrcSpan -> Bool
hasSrcSpanFile NoSrcSpan = False
hasSrcSpanFile _         = True

-- | Tests whether the given source span has attached source code.
hasSourceCode :: SrcSpan -> Bool
hasSourceCode NoSrcSpan          = False
hasSourceCode (FileSpan _)       = False
hasSourceCode srcSpan@SrcSpan {} = not (null (srcSpanCodeLines srcSpan))

-- | Tests whether the given source span spans multiple lines.
spansMultipleLines :: SrcSpan -> Bool
spansMultipleLines NoSrcSpan = False
spansMultipleLines (FileSpan _) = False
spansMultipleLines SrcSpan { srcSpanStartLine = start, srcSpanEndLine = end }
  = start /= end

-------------------------------------------------------------------------------
-- Conversion                                                                --
-------------------------------------------------------------------------------
-- | Type class for source spans from other packages that can be converted
--   to 'SrcSpan's for pretty printing of messages.
class ConvertibleSrcSpan ss where
  -- | Converts the given third party source span to a 'SrcSpan' by attaching
  --   the corresponding line of source code.
  convertSrcSpan :: SrcFileMap -> ss -> SrcSpan

-------------------------------------------------------------------------------
-- Pretty Printing Source Spans                                              --
-------------------------------------------------------------------------------
-- | Pretty instance for a source file that displays the filename.
instance Pretty SrcFile where
  pretty = prettyString . srcFileName

-- | Pretty instance for a source span that displays the filename and the start
--   and end position of the source span.
--
--   If the source span spans only a single line, the end position is omitted.
instance Pretty SrcSpan where
  pretty NoSrcSpan          = prettyString "<no location info>"
  pretty (FileSpan srcFile) = prettyString (srcFileName srcFile)
  pretty srcSpan
    | spansMultipleLines srcSpan = pretty (srcSpanFile srcSpan)
      <> colon
      <> int (srcSpanStartLine srcSpan)
      <> colon
      <> int (srcSpanStartColumn srcSpan)
      <> char '-'
      <> int (srcSpanEndLine srcSpan)
      <> colon
      <> int (srcSpanEndColumn srcSpan)
    | otherwise = pretty (srcSpanFile srcSpan)
      <> colon
      <> int (srcSpanStartLine srcSpan)
      <> colon
      <> int (srcSpanStartColumn srcSpan)
