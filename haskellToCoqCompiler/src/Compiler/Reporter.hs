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
  , addMessages
  , foldReporter
  , isFatal
  , mapLocation
  , messages
  , printMessage
  , printMessages
  , report
  , reportFatal
  )
where

import           Control.Monad                  ( liftM
                                                , ap
                                                )
import qualified Data.Text.Lazy                as TL
import           Text.PrettyPrint.Leijen.Text
import           System.IO

import           Language.Haskell.Exts.SrcLoc   ( SrcSpan
                                                , SrcInfo(..)
                                                , spanSize
                                                )

-------------------------------------------------------------------------------
-- Messages                                                                  --
-------------------------------------------------------------------------------

-- | The severity of a message reported by the compiler.
data Severity = Error | Warning | Info

-- | A message reported by the compiler.
--
--   'l' is the type of the location annotation. The location annotation
--   carries information about the position in the source file of the code
--   that caused the message to be reported.
data Message l = Message l Severity String

-- | Applies the given function on the location annotation of a message.
--
--   The main pupose of this function is to aid in pretty printing messages.
--   The location annotation of the messages passed to 'printMessage' must
--   be a 'SrcSpan's from @haskell-src-ext@. Sometimes we have a location
--   annotation of a different type. In such cases @mapLocation@ must be
--   applied to convert the location annotation.
mapLocation :: (l -> l') -> Message l -> Message l'
mapLocation f (Message loc severity msg) = Message (f loc) severity msg

-------------------------------------------------------------------------------
-- Reporter monad                                                            --
-------------------------------------------------------------------------------

-- | A data structure that contains the messages reported by the compiler
--   and an optional value that is present only if the compiler did not
--   encounter a fatal error.
--
--   The message lists are in reverse order, i.e. the last reported
--   message comes first. In case of 'Fatal' that mesan that the head
--   of the message list contains the reason for the failure.
data Reporter l a =
  Report [Message l] a
  | Fatal [Message l]

-- | Functor instance for 'Reporter's to allow creation of the
--   'Applicative' instance.
instance Functor (Reporter l) where
  fmap = liftM

-- | Applicative instance for 'Reporter's to allow creation of the
--   'Monad' instance.
instance Applicative (Reporter l) where
  pure = return
  (<*>) = ap

-- | Monad instance for 'Reporter's.
--
--   When two reporters are executed in sequence, the resulting reporter
--   reports all messages of both reporters. The messages reported by the
--   second reporter will occur before.
--
--   When a reporter encounters a fatal error, no subsequent reporters are
--   executed.
instance Monad (Reporter l) where
  return = Report []
  (>>=) (Report ms x) f = addMessages (f x) ms
  (>>=) (Fatal ms) _ = Fatal ms

-------------------------------------------------------------------------------
-- Reporting messages                                                        --
-------------------------------------------------------------------------------

-- | Appends a list of messages to the messages reported by the given reporter.
--
--   The new messages are added to the back of the message list.
addMessages :: Reporter l a -> [Message l] -> Reporter l a
addMessages (Report ms x) ms' = Report (ms ++ ms') x
addMessages (Fatal ms   ) ms' = Fatal (ms ++ ms')

-- | Creates a successful reporter that reports the given message.
report :: Message l -> Reporter l ()
report msg = Report [msg] ()

-- | Creates a reporter that fails with the given message.
reportFatal :: Message l -> Reporter l a
reportFatal msg = Fatal [msg]

-------------------------------------------------------------------------------
-- Handling messages and reporter results                                    --
-------------------------------------------------------------------------------

-- | Tests whether a fatal error was reported to the given reporter.
isFatal :: Reporter l a -> Bool
isFatal (Report _ _) = False
isFatal (Fatal _   ) = True

-- | Gets the messages reported to the given reporter.
--
--   Because the reporter stores messages in reverse order (i.e. the head of
--   the stored list is the latest message) this function reverses the message
--   list such taht it is in the right order again (i.e. the head of the
--   returned list is the first message).
messages :: Reporter l a -> [Message l]
messages (Report ms _) = reverse ms
messages (Fatal ms   ) = reverse ms

-- | Handles the result of a reporter by invoking the given function or
--   returning the provided default value depending on whether a fatal
--   error was reported or not.
foldReporter
  :: Reporter l a
  -> (a -> b)  -- ^ The function to apply if no fatal error was encountered.
  -> b         -- ^ The value to return if a fatal error was encountered.
  -> b
foldReporter (Report _ x) f _ = f x
foldReporter (Fatal _   ) _ v = v

-------------------------------------------------------------------------------
-- Printing messages                                                         --
-------------------------------------------------------------------------------

-- | Gets the label to print before the text of a message of the given
--   severity.
severityLabel :: Severity -> String
severityLabel Error   = "error"
severityLabel Warning = "warning"
severityLabel Info    = "info"

-- | Prints the given message to @stdout@.
--
--   The location annotation of the message must be
printMessage :: Message SrcSpan -> IO ()
printMessage (Message loc severity msg) = do
  -- TODO Use ANSI escape sequences to format message.
  -- TODO Can we avoid to read the input file again?
  contents <- readFile (fileName loc)
  let code = lines contents !! (startLine loc - 1)
      doc  = locDoc <+> severityDoc <$$> msgDoc <$$> codeDoc code <> line
  displayIO stdout (renderPretty ribbonFrac maxLineWidth doc)
 where
  -- | The maximum line width that must no be exceeded by the message text.
  --
  --   This is configured to be 80 characters, because on most platforms
  --   terminals have a default width of 80 columns.
  maxLineWidth :: Int
  maxLineWidth = 80

  -- | The whole line is allowed be occupied by non-indentation characters.
  ribbonFrac :: Float
  ribbonFrac = 1.0

  -- | Document for the start of the source span with trailing colon.
  locDoc :: Doc
  locDoc =
    text (TL.pack (fileName loc))
      <> colon
      <> int (startLine loc)
      <> colon
      <> int (startColumn loc)
      <> colon

  -- | Document for the severity label with trailing colon.
  severityDoc :: Doc
  severityDoc = text (TL.pack (severityLabel severity)) <> colon

  -- | Document for the message text.
  --
  --   The message is indented by four spaces. The individual words of the
  --   messages are concatenated with 'softline's, such that the text is
  --   broken into multiple lines if it does not fit into a line of the
  --   configured 'width'.
  msgDoc :: Doc
  msgDoc = indent 4 (foldr (</>) empty (map (text . TL.pack) (words msg)))

  -- | Document that displays the given line of code, the line number and
  --   highlights the source span using 'caret's.
  codeDoc :: String -> Doc
  codeDoc code =
    gutterDoc
      <$$> lineNumberDoc
      <+>  text (TL.pack code)
      <$$> gutterDoc
      <>   highlightDoc

  -- | Document for the line number including padding and the leading pipe.
  lineNumberDoc :: Doc
  lineNumberDoc = space <> int (startLine loc) <> space <> pipe

  -- | The width of the column that contains the line number of the 'codeDoc'
  --   including the padding before and after the line number.
  gutterWidth :: Int
  gutterWidth = length (show (startLine loc)) + 2

  -- | Document with the same length as 'lineNumberDoc' but without the line
  --   number.
  gutterDoc :: Doc
  gutterDoc = indent gutterWidth pipe

  -- | Document that contains 'caret' signs to highligh the source span.
  highlightDoc :: Doc
  highlightDoc =
    indent (startColumn loc) (hcat (replicate (snd (spanSize loc)) caret))

  -- | Document that contains the pipe character @|@.
  pipe :: Doc
  pipe = text (TL.pack "|")

  -- | Document that contains the caret character @^@.
  caret :: Doc
  caret = text (TL.pack "^")

-- | Prints all given messages to @stdout@.
printMessages :: [Message SrcSpan] -> IO ()
printMessages = mapM_ printMessage
