{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains utility functions for working with the Parsec
--   library.
module FreeC.Util.Parsec where

import           Data.Composition     ( (.:) )
import           Text.Parsec          ( Parsec )
import qualified Text.Parsec          as Parsec
import qualified Text.Parsec.Error    as Parsec

import           FreeC.IR.SrcSpan
import           FreeC.Monad.Reporter

-- | Converts a Parsec 'Parsec.SourcePos' to a 'SrcSpan'.
instance ConvertibleSrcSpan Parsec.SourcePos where
  convertSrcSpan srcPos = SrcSpan
    { srcSpanFilename    = Parsec.sourceName srcPos
    , srcSpanStartLine   = Parsec.sourceLine srcPos
    , srcSpanStartColumn = Parsec.sourceColumn srcPos
    , srcSpanEndLine     = Parsec.sourceLine srcPos
    , srcSpanEndColumn   = Parsec.sourceColumn srcPos
    , srcSpanCodeLines   = []
    }

-- | Converts a 'Parsec.ParseError' to an error 'Message'.
--
--   The error message can quote source code from the given source files.
parsecErrorToMessage :: SrcFileMap -> Parsec.ParseError -> Message
parsecErrorToMessage srcFiles parseError = Message
  (addSourceCode srcFiles (convertSrcSpan (Parsec.errorPos parseError))) Error
  (Parsec.showErrorMessages msgOr msgUnknown msgExpecting msgUnExpected
   msgEndOfInput (Parsec.errorMessages parseError))
 where
   msgOr, msgUnknown, msgExpecting, msgUnExpected, msgEndOfInput :: String
   msgOr = "or"

   msgUnknown = "unknown parse error"

   msgExpecting = "expecting"

   msgUnExpected = "unexpected"

   msgEndOfInput = "end of input"

-- | Reports a fatal 'Parsec.ParseError'.
--
--   The error message can quote source code from the given source files.
reportParsecError :: MonadReporter r => SrcFileMap -> Parsec.ParseError -> r a
reportParsecError = reportFatal .: parsecErrorToMessage

-- | Runs the given parser on the given input and reports a fatal error
--   if there is a parse error.
runParsecOrFail :: MonadReporter r => SrcFile         -- ^ The file to parse.
  -> [t]             -- ^ The token stream to parse.
  -> Parsec [t] () a -- ^ The parser to run.
  -> r a
runParsecOrFail srcFile stream parser = do
  let srcFiles = mkSrcFileMap [srcFile]
      result   = Parsec.runParser parser () (srcFileName srcFile) stream
  either (reportParsecError srcFiles) return result
