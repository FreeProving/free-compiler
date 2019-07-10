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
  ( -- * Messages
    Message(..)
  , Severity(..)
    -- * Reporter monad
  , Reporter
  , runReporter
    -- * Reporter monad transformer
  , ReporterT
  , runReporterT
  , lift
  , hoist
  , unhoist
    -- * Reporting messages
  , report
  , reportFatal
    -- * Reporting IO errors
  , ReporterIO
  , reportIOErrors
  , reportIOError
    -- * Handling messages and reporter results
  , isFatal
  , messages
    -- * Handling reportedmessages
  , reportTo
  , reportToOrExit
  )
where

import           Control.Monad                  ( liftM
                                                , ap
                                                )
import           Control.Monad.Identity
import           Control.Monad.Trans.Maybe
import           Control.Monad.Writer
import           Data.Maybe                     ( isNothing
                                                , maybe
                                                )
import           System.Exit                    ( exitFailure )
import           System.IO                      ( Handle )
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
data Severity = Internal | Error | Warning | Info
  deriving (Eq, Show)

-- | A message reported by the compiler.
data Message = Message (Maybe SrcSpan) Severity String
  deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Reporter monad                                                            --
-------------------------------------------------------------------------------

-- | The underlying representation of a reporter.
type UnwrappedReporter = MaybeT (Writer [Message])

-- | A monad that collects the messages reported by the compiler and contains
--   an optional value that is present only if the compiler did not encounter
--   a fatal error.
--
--   This type behaves like @(Maybe a, [Message])@.
type Reporter = ReporterT Identity

-- | Gets the underlying representation of the given reporter.
unwrapReporter :: Reporter a -> UnwrappedReporter a
unwrapReporter = runIdentity . unwrapReporterT

-- | Runs the given reporter and returns the produced value as well as all
--   reported messages. If a fatal message has been reported the produced
--   value is @Nothing@.
runReporter :: Reporter a -> (Maybe a, [Message])
runReporter = runIdentity . runReporterT

-------------------------------------------------------------------------------
-- Reporter monad transformer                                                --
-------------------------------------------------------------------------------

-- | A reporter monad parameterized by the inner monad @m@.
newtype ReporterT m a = ReporterT { unwrapReporterT :: m (UnwrappedReporter a) }

-- | Runs the given reporter and returns the produced value as well as all
--   reported messages. If a fatal message has been reported the produced
--   value is @Nothing@. The result is wrapped in the inner monad.
runReporterT :: Monad m => ReporterT m a -> m (Maybe a, [Message])
runReporterT rmx = unwrapReporterT rmx >>= (return . runWriter . runMaybeT)

-- | The @Functor@ instance for 'ReporterT' is needed to define the @Monad@
--   instance.
instance Monad m => Functor (ReporterT m) where
  fmap = liftM

-- | The @Applicative@ instance for 'ReporterT' is needed to define the @Monad@
--   instance.
instance Monad m => Applicative (ReporterT m) where
  pure = return
  (<*>) = ap

-- | The @Monad@ instance for @ReporterT@.
--
--   'fail' is overwritten such that internal errors (e.g. pattern matching
--   failures in @do@-blocks) are caught.
instance Monad m => Monad (ReporterT m) where
  fail = reportFatal . Message Nothing Internal
  return = ReporterT . return . return
  (>>=) rt f = ReporterT $ do
     (mx, ms) <- runReporterT rt
     (mx', ms') <- maybe (return (Nothing, [])) (runReporterT . f) mx
     return (MaybeT (writer (mx', ms ++ ms')))

-- | @MonadTrans@ instance for 'ReporterT'.
instance MonadTrans ReporterT where
 lift mx = ReporterT (mx >>= return . return)

-- | Lifts a reporter to any reporter transformer.
hoist :: Monad m => Reporter a -> ReporterT m a
hoist = ReporterT . return . unwrapReporter

-- | Undoes 'hoist'.
unhoist :: Monad m => ReporterT m a -> m (Reporter a)
unhoist rt = do
  u <- unwrapReporterT rt
  return (ReporterT (Identity u))

-------------------------------------------------------------------------------
-- Reporting messages                                                        --
-------------------------------------------------------------------------------

-- | Creates a successful reporter that reports the given message.
report :: Monad m => Message -> ReporterT m ()
report = ReporterT . return . lift . tell . (: [])

-- | Creates a reporter that fails with the given message.
reportFatal :: Monad m => Message -> ReporterT m a
reportFatal = ReporterT . return . (>> mzero) . lift . tell . (: [])

-------------------------------------------------------------------------------
-- Reporting IO errors                                                       --
-------------------------------------------------------------------------------

-- | A reporter with an IO action as its inner monad.
type ReporterIO = ReporterT IO

-- | IO actions can be embedded into reporters.
instance MonadIO m => MonadIO (ReporterT m) where
  liftIO action = ReporterT $ do
     x <- liftIO action
     return (return x)

-- | Creates an IO action for a reporter that reports all IO errors that
--   that occur during the given IO action.
--
--   All IO errors are considered fatal and have no location information.
reportIOErrors :: ReporterIO a -> ReporterIO a
reportIOErrors =
  ReporterT
    . flip catchIOError (return . unwrapReporter . reportIOError)
    . unwrapReporterT

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
isFatal = isNothing . fst . runReporter

-- | Gets the messages reported to the given reporter.
messages :: Reporter a -> [Message]
messages = snd . runReporter

-------------------------------------------------------------------------------
-- Handling reported messages                                                --
-------------------------------------------------------------------------------

-- | Runs the given reporter and prints all reported messages to the
--   provided file handle.
reportTo :: MonadIO m => Handle -> ReporterT m a -> m (Maybe a)
reportTo h reporter = do
  (mx, messages) <- runReporterT reporter
  liftIO $ hPutPretty h messages
  return mx

-- | Runs the given reporter, prints all reported messages to @stderr@ and
--   exits the application if a fatal message has been reported.
reportToOrExit :: MonadIO m => Handle -> ReporterT m a -> m a
reportToOrExit h reporter = do
  mx <- reportTo h reporter
  case mx of
    Nothing -> liftIO exitFailure
    Just x  -> return x

-------------------------------------------------------------------------------
-- Pretty printing messages                                                  --
-------------------------------------------------------------------------------

-- | Pretty instance for message severity levels.
instance Pretty Severity where
  pretty Internal = prettyString "internal error"
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
