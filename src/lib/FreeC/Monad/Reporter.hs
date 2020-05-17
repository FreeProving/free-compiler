-- | This module contains the definition of a monad that is used by the
--   compiler to report error messages, warnings and hints to the user
--   without throwing an exception or performing IO actions.
--
--   During execution the 'Reporter' monad collects all reported messages
--   internally. Additionally the monad holds the result of the computation.
--   The computation can be interrupted without returning a result by reporting
--   a fatal error message.
--
--   The 'ReporterT' monad transformer is used to implement 'ReporterIO' which
--   simplifies combining IO actions with error reporting.
--
--   This module also provides functions for pretty printing the collected
--   error messages in a similar way to how the GHC prints error messages.

module FreeC.Monad.Reporter
  ( -- * Messages
    Message(..)
  , Severity(..)
    -- * Reporter monad
  , Reporter
  , runReporter
  , evalReporter
    -- * Reporter monad transformer
  , ReporterT
  , runReporterT
  , lift
  , hoist
  , unhoist
    -- * Reporting messages
  , MonadReporter(..)
  , report
  , reportFatal
    -- * Reporting IO errors
  , ReporterIO
  , liftIO
  , reportIOError
    -- * Handling messages and reporter results
  , isFatal
  , messages
    -- * Handling reported messages
  , reportTo
  , reportToOrExit
  )
where

import           Control.Monad                  ( (<=<)
                                                , ap
                                                , liftM
                                                , mzero
                                                )
import           Control.Monad.Fail             ( MonadFail(..) )
import           Control.Monad.Identity         ( Identity(..) )
import           Control.Monad.Trans.Maybe      ( MaybeT(..) )
import           Control.Monad.Writer           ( Writer
                                                , MonadIO(..)
                                                , MonadTrans(..)
                                                , runWriter
                                                , tell
                                                , writer
                                                )
import           Data.Maybe                     ( isNothing
                                                , maybe
                                                )
import           System.Exit                    ( exitFailure )
import           System.IO                      ( Handle )
import           System.IO.Error                ( catchIOError
                                                , ioeGetErrorString
                                                , ioeGetFileName
                                                )

import           FreeC.IR.SrcSpan
import           FreeC.Monad.Class.Hoistable
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Messages                                                                  --
-------------------------------------------------------------------------------

-- | The severity of a message reported by the compiler.
data Severity = Internal | Error | Warning | Info
  deriving (Eq, Show)

-- | A message reported by the compiler.
data Message = Message SrcSpan Severity String
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

-- | Like 'runReporter' but discards the reported messages.
evalReporter :: Reporter a -> Maybe a
evalReporter = fst . runReporter

-------------------------------------------------------------------------------
-- Reporter monad transformer                                                --
-------------------------------------------------------------------------------

-- | A reporter monad parameterized by the inner monad @m@.
newtype ReporterT m a = ReporterT { unwrapReporterT :: m (UnwrappedReporter a) }

-- | Runs the given reporter and returns the produced value as well as all
--   reported messages. If a fatal message has been reported the produced
--   value is @Nothing@. The result is wrapped in the inner monad.
runReporterT :: Monad m => ReporterT m a -> m (Maybe a, [Message])
runReporterT rmx = runWriter . runMaybeT <$> unwrapReporterT rmx

-- | The @Functor@ instance for 'ReporterT' is needed to define the @Monad@
--   instance.
instance Monad m => Functor (ReporterT m) where
  fmap = liftM

-- | The @Applicative@ instance for 'ReporterT' is needed to define the @Monad@
--   instance.
instance Monad m => Applicative (ReporterT m) where
  pure  = return
  (<*>) = ap

-- | The @Monad@ instance for @ReporterT@.
instance Monad m => Monad (ReporterT m) where
  return = ReporterT . return . return
  (>>=) rt f = ReporterT $ do
    (mx , ms ) <- runReporterT rt
    (mx', ms') <- maybe (return (Nothing, [])) (runReporterT . f) mx
    return (MaybeT (writer (mx', ms ++ ms')))

-- | @MonadTrans@ instance for 'ReporterT'.
instance MonadTrans ReporterT where
  lift mx = ReporterT (return <$> mx)

-- | The reporter monad can be lifted to any reporter transformer.
instance Hoistable ReporterT where
  hoist = ReporterT . return . unwrapReporter

-- | @hoist@ can be undone for reporters.
instance UnHoistable ReporterT where
  unhoist = fmap (ReporterT . Identity) . unwrapReporterT

-------------------------------------------------------------------------------
-- Reporting messages                                                        --
-------------------------------------------------------------------------------

-- | Type class for all monads within which 'Message's can be reported.
class Monad r => MonadReporter r where
  -- | Promotes a reporter to @r@.
  liftReporter :: Reporter a -> r a

-- | Reporters can be trivially promoted to any reporter transformer.
instance Monad m => MonadReporter (ReporterT m) where
  liftReporter = hoist

-- | Creates a successful reporter that reports the given message.
report :: MonadReporter r => Message -> r ()
report = liftReporter . ReporterT . Identity . lift . tell . (: [])

-- | Creates a reporter that fails with the given message.
reportFatal :: MonadReporter r => Message -> r a
reportFatal =
  liftReporter . ReporterT . Identity . (>> mzero) . lift . tell . (: [])

-- | Internal errors (e.g. pattern matching failures in @do@-blocks) are
--   cause fatal error messages to be reported.
instance Monad m => MonadFail (ReporterT m) where
  fail = reportFatal . Message NoSrcSpan Internal

-------------------------------------------------------------------------------
-- Reporting IO errors                                                       --
-------------------------------------------------------------------------------

-- | A reporter with an IO action as its inner monad.
type ReporterIO = ReporterT IO

-- | IO actions can be embedded into reporters.
--
--   If an IO error occurs, a fatal error is reported by the reporter instead.
--   IO errors do not have location information (see also 'reportIOError').
instance MonadIO m => MonadIO (ReporterT m) where
  liftIO = handleIOErrors <=< (lift . liftIO . wrapIOErrors)
   where
    -- | Catches IO errors thrown by the given IO action and returns either
    --   the caught error or the returned value.
    wrapIOErrors :: IO a -> IO (Either IOError a)
    wrapIOErrors = flip catchIOError (return . Left) . fmap Right

    -- Handles IO errors thrown by the original IO action (which have been
    -- wrapped by 'wrapIOErrors') by reporting a fatal error.
    handleIOErrors :: MonadReporter r => Either IOError a -> r a
    handleIOErrors (Left  err) = reportIOError err
    handleIOErrors (Right x  ) = return x

-- | Reports the given IO error as a fatal error with no location information.
reportIOError :: MonadReporter r => IOError -> r a
reportIOError = reportFatal . Message NoSrcSpan Error . ioErrorMessageText
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
--
--   If the inner monad of the reporter is an IO action, the IO action will
--   be executed before the messages are printed to the file handle.
--   To run an IO action after the messages have been reported, the reporter
--   needs to return the IO action (e.g. @Reporter (IO ())@ instead of
--   @ReporterIO ()@). It is possible to combine both approaches (i.e. run an
--   IO action before the messages are printed and another action afterwards)
--   by using @ReporterIO (IO ())@. In the latter case this function returns
--   a value of type @IO (IO ())@. Thus an additional @join@ is needed:
--   @join (reportTo h reporter)@.
reportTo :: MonadIO m => Handle -> ReporterT m a -> m (Maybe a)
reportTo h reporter = do
  (mx, ms) <- runReporterT reporter
  liftIO $ hPutPretty h ms
  return mx

-- | Runs the given reporter, prints all reported messages to @stderr@ and
--   exits the application if a fatal message has been reported.
--
--   See 'reportTo' for usage information.
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
  pretty Error    = prettyString "error"
  pretty Warning  = prettyString "warning"
  pretty Info     = prettyString "info"

-- | Pretty instance for messages.
--
--   The format of the messages is based on the format used by GHC:
--
--   > [file]:[line]:[column]: [severity]:
--   >     [message-contents]
--   >        |
--   > [line] | [line of code ... culprit  ... ]
--   >        |                   ^^^^^^^
--
--   If no location information is attached to the message, a place holder is
--   text displayed instead of the filename, and start position and no
--   code snippet will be shown.
--
--   Lists of messages are separated by a newline.
instance Pretty Message where
  pretty (Message srcSpan severity msg) =
    (pretty srcSpan <> colon)
      <+>  (pretty severity <> colon)
      <$$> indent 4 (prettyLines msg)
      <>   line
      <>   prettyCodeBlock srcSpan
  prettyList = prettySeparated line

-- | Creates a document that shows the line of code that caused a message to
--   be reported.
--
--   If the message contains no location information or no source code the
--   empty document is returned.
prettyCodeBlock :: SrcSpan -> Doc
prettyCodeBlock srcSpan
  | hasSourceCode srcSpan
  = gutterDoc
    <$$> firstLineNumberDoc
    <+>  prettyString firstLine
    <$$> gutterDoc
    <>   highlightDoc
    <>   ellipsisDoc
    <>   line
  | otherwise
  = empty
 where
  -- | The first line of source code spanned by the given source span.
  firstLine :: String
  firstLine = head (srcSpanCodeLines srcSpan)

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
    = length firstLine - srcSpanStartColumn srcSpan + 1
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
