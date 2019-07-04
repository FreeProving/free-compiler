-- | This module contains the definition of a monad that is used by the
--   compiler to report error messages, warnings and hints to the user
--   without throwing an exception or performing IO actions.
--
--   During execution the 'Reporter' monad collects all reported messages
--   internally. Additionally the monad holds the result of the computation.
--   The computation can be interrupted without returning a result by reporting
--   a fatal error message.
--
--   This module also provides functions for pretty printing the collected
--   error messages in a similar way to how the GHC prints error messages.

module Compiler.Reporter
  ( Message(..)
  , Reporter
  , Severity(..)
  , foldReporter
  , isFatal
  , messages
  , report
  , reportFatal
  , reportIOErrors
  , reportIOError
  )
where

import           Control.Monad.Trans.Maybe
import           Control.Monad.Writer
import           Data.Maybe                     ( isNothing
                                                , maybe
                                                )
import           System.IO.Error                ( catchIOError
                                                , ioeGetErrorString
                                                , ioeGetFileName
                                                )

import           Compiler.Pretty
import           Compiler.SrcSpan

-------------------------------------------------------------------------------
-- Messages                                                                  --
-------------------------------------------------------------------------------

-- | The severity of a message reported by the compiler.
data Severity = Error | Warning | Info

-- | A message reported by the compiler.
data Message = Message (Maybe SrcSpan) Severity String

-------------------------------------------------------------------------------
-- Reporter monad                                                            --
-------------------------------------------------------------------------------

-- | A monad that collects the messages reported by the compiler and contains
--   an optional value that is present only if the compiler did not encounter
--   a fatal error.
--
--   This type behaves like @(Maybe a, w)@.
type Reporter a = MaybeT (Writer [Message]) a

-------------------------------------------------------------------------------
-- Reporting messages                                                        --
-------------------------------------------------------------------------------

-- | Creates a successful reporter that reports the given message.
report :: Message -> Reporter ()
report = MaybeT . fmap Just . tell . (: [])

-- | Creates a reporter that fails with the given message.
reportFatal :: Message -> Reporter a
reportFatal = MaybeT . fmap (const Nothing) . tell . (: [])

-- | Creates an IO action for a reporter that reports all IO errors that
--   that occur during the given IO action.
--
--   All IO errors are considered fatal and have no location information.
reportIOErrors :: IO (Reporter a) -> IO (Reporter a)
reportIOErrors action = catchIOError action (return . reportIOError)

-- | Reports the given IO error as a fatal error with no location information.
reportIOError :: IOError -> Reporter a
reportIOError = reportFatal . Message Nothing Error . ioErrorMessageText
 where
  ioErrorMessageText :: IOError -> String
  ioErrorMessageText err =
    ioeGetErrorString err ++ maybe "" (": " ++) (ioeGetFileName err)

-------------------------------------------------------------------------------
-- Handling messages and reporter results                                    --
-------------------------------------------------------------------------------

-- | Tests whether a fatal error was reported to the given reporter.
isFatal :: Reporter a -> Bool
isFatal = isNothing . fst . runWriter . runMaybeT

-- | Gets the messages reported to the given reporter.
messages :: Reporter a -> [Message]
messages = execWriter . runMaybeT

-- | Handles the result of a reporter by invoking the given function or
--   returning the provided default value depending on whether a fatal
--   error was reported or not.
foldReporter
  :: Reporter a
  -> (a -> b)  -- ^ The function to apply if no fatal error was encountered.
  -> b         -- ^ The value to return if a fatal error was encountered.
  -> b
foldReporter reporter f v =
  maybe v f (fst (runWriter (runMaybeT reporter)))

-------------------------------------------------------------------------------
-- Pretty printing messages                                                  --
-------------------------------------------------------------------------------

-- | Pretty instance for message severity levels.
instance Pretty Severity where
  pretty Error   = prettyString "error"
  pretty Warning = prettyString "warning"
  pretty Info    = prettyString "info"

-- | Pretty instance for messages.
--
--   The format of the messages is based on the format used by GHC:
--
--   @
--   <file>:<line>:<column>: <severity>:
--       <message-contents>
--          |
--   <line> | <line of code ... culprit  ... >
--          |                   ^^^^^^^
--   @
--
--   If no location information is attached to the message, a place holder is
--   text displayed instead of the filename, and start position and no
--   code snippet will be shown.
--
--   Lists of messages are separated by a newline.
instance Pretty Message where
  pretty (Message maybeSrcSpan severity msg) =
    (prettyMaybe "<no location info>" maybeSrcSpan <> colon)
      <+>  (pretty severity <> colon)
      <$$> (indent 4 $ prettyText msg)
      <>   line
      <>   prettyCodeBlock maybeSrcSpan
  prettyList = prettySeparated line

-- | Creates a document that shows the line of code that caused a message to
--   be reported.
--
--   If the message contains no location information or no source code the
--   empty document is returned.
prettyCodeBlock :: Maybe SrcSpan -> Doc
prettyCodeBlock Nothing = empty
prettyCodeBlock (Just SrcSpan { srcSpanCodeLines = [] }) = empty
prettyCodeBlock (Just srcSpan@SrcSpan { srcSpanCodeLines = (code : _) }) =
  gutterDoc
    <$$> firstLineNumberDoc
    <+>  prettyString code
    <$$> gutterDoc
    <>   highlightDoc
    <>   ellipsisDoc
    <>   line
 where
  -- | Document for the first line number covered by the source span including
  --   padding and a trailing pipe symbol.
  firstLineNumberDoc :: Doc
  firstLineNumberDoc = space <> int (srcSpanStartLine srcSpan) <> space <> pipe

  -- | Document with the same length as 'firstLineNumberDoc' but does
  --   contain only spaces before the pipe character.
  gutterDoc :: Doc
  gutterDoc =
    let gutterWidth = length (show (srcSpanStartLine srcSpan)) + 2
    in  indent gutterWidth pipe

  -- | Document that contains 'caret' signs to highligh the code in the
  --   first line that is covered by the source span.
  highlightDoc :: Doc
  highlightDoc = indent (srcSpanStartColumn srcSpan)
                        (hcat (replicate highlightWidth caret))

  -- The number of characters in the the first line of the source span.
  highlightWidth :: Int
  highlightWidth
    | isMultiLine
    = length code - srcSpanStartColumn srcSpan + 1
    | otherwise
    = max 1 $ srcSpanEndColumn srcSpan - srcSpanStartColumn srcSpan

  -- | Document added after the 'highlightDoc' if the source span coveres
  --   more than one line.
  ellipsisDoc :: Doc
  ellipsisDoc | isMultiLine = prettyString "..."
              | otherwise   = empty

  -- | Whether the source span covers more than one line.
  isMultiLine :: Bool
  isMultiLine = spansMultipleLines srcSpan

  -- | Document that contains the pipe character @|@.
  pipe :: Doc
  pipe = char '|'

  -- | Document that contains the caret character @^@.
  caret :: Doc
  caret = char '^'
