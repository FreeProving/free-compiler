{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances
           , FunctionalDependencies #-}

-- | This module contains a type class for monads that can be used in tests.

module FreeC.Monad.Class.Testable
  ( MonadTestable
    -- * Expecting values
  , shouldReturn
  , shouldReturnWith
    -- * Expecting success
  , shouldSucceed
  , shouldSucceedWith
    -- * Expecting failures
  , shouldFail
  , shouldFailWith
    -- * QuickCheck
  , shouldReturnProperty
  )
where

import           Control.Monad.IO.Class         ( MonadIO )
import           Data.List                      ( intercalate )
import           Data.IORef                     ( IORef
                                                , newIORef
                                                , readIORef
                                                , writeIORef
                                                )
import           System.IO.Error                ( catchIOError
                                                , ioeGetErrorString
                                                , ioeGetFileName
                                                )
import           System.IO.Unsafe               ( unsafePerformIO )
import           Test.Hspec              hiding ( shouldReturn )
import           Test.HUnit.Base                ( assertFailure )
import           Test.QuickCheck

import           Data.Functor.Identity          ( Identity(..) )

import           FreeC.Environment
import           FreeC.Environment.ModuleInterface
import           FreeC.Environment.ModuleInterface.Decoder
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-- | Type class for monads which can be used in tests.
class Monad m => MonadTestable m err | m -> err where
  -- | Like 'shouldReturnWith' but uses the first argument for pretty printing.
  shouldReturnWith'
    :: (a -> String)      -- ^ Function to use to print unexpected values.
    -> m a                -- ^ The computation to set the expectation for.
    -> (a -> IO b)        -- ^ Sets the expectation for a value.
    -> IO b

  -- | Like 'shouldFailWith' but uses the first argument for pretty printing.
  shouldFailWith'
    :: (a -> String)        -- ^ Function to use to print unexpected values.
    -> m a                  -- ^ The computation to set the expectation for.
    -> (err -> IO b)        -- ^ Sets the expectation for the produced error.
    -> IO b

-- | Sets the expectation returned by the given function for the value
--   returned by the given computation.
shouldReturnWith
  :: (Show a, MonadTestable m err) => m a -> (a -> Expectation) -> Expectation
shouldReturnWith = shouldReturnWith' show

-- | Sets the expectation that the given computation successfully returns
--   the given value.
shouldReturn :: (Eq a, Show a, MonadTestable m err) => m a -> a -> Expectation
shouldReturn mx y = shouldReturnWith mx (`shouldBe` y)

-- | Sets the expectation that the given computation does not fail.
shouldSucceed :: (Show a, MonadTestable m err) => m a -> Expectation
shouldSucceed mx = shouldSucceedWith (return () <$ mx)

-- | Sets the expectation that the given computation successfully produces
--   an expectation and that expectation holds.
shouldSucceedWith :: (MonadTestable m err) => m Expectation -> Expectation
shouldSucceedWith = flip (shouldReturnWith' (const "<expectation>")) id

-- | Sets the expectation that the given computation fails without returning
--   a value.
shouldFail :: (Show a, MonadTestable m err) => m a -> Expectation
shouldFail = flip shouldFailWith (const (return ()))

-- | Sets the expectation returned by the given function for the error
--   that was produced by the given computation instead of a value.
shouldFailWith
  :: (Show a, MonadTestable m err) => m a -> (err -> Expectation) -> Expectation
shouldFailWith = shouldFailWith' show

-------------------------------------------------------------------------------
-- Instances for common pure monads                                          --
-------------------------------------------------------------------------------

-- | A computation in the @Identity@ monad can return a result but never fails.
instance MonadTestable Identity () where
  shouldReturnWith' _ = flip ($) . runIdentity
  shouldFailWith' _ _ _ =
    assertFailure "Expected failure, but the Identity monad cannot fail."

-- | A computation in the @Maybe@ monad fails if the result is @Nothing@ and
--   succeeds if the result is @Just@ a value.
instance MonadTestable Maybe () where
  shouldReturnWith' _ (Just x) f = f x
  shouldReturnWith' _ Nothing _ =
    assertFailure "Unexpected failure in Maybe monad."
  shouldFailWith' _ Nothing f = f ()
  shouldFailWith' showValue (Just x) _ =
    assertFailure
      $  "Expected failure in Maybe monad, "
      ++ "but the following value was produced: "
      ++ showValue x

-- | A computation in the @Either@ monad fails if the result is @Left@ and
--   succeeds if the result is @Right@.
instance Show err => MonadTestable (Either err) err where
  shouldReturnWith' _ (Right x) f = f x
  shouldReturnWith' _ (Left err) _ =
    assertFailure $ "Unexpected failure in Either monad, got " ++ show err
  shouldFailWith' _ (Left err) f = f err
  shouldFailWith' showValue (Right x) _ =
    assertFailure
      $  "Expected failure in Either monad, "
      ++ "but the following value was produced: "
      ++ showValue x

-------------------------------------------------------------------------------
-- Instance for the IO monad                                                 --
-------------------------------------------------------------------------------

-- | An impure computation in the @IO@ monad fails if an @IO@ error is thrown.
instance MonadTestable IO IOError where
  shouldReturnWith' _ mx f = catchIOError (mx >>= f) $ \err ->
    assertFailure $ "Unexpected IO error: " ++ ioeGetErrorString err ++ maybe
      ""
      (": " ++)
      (ioeGetFileName err)
  shouldFailWith' showValue mx f = flip catchIOError f $ do
    x <- mx
    assertFailure
      $  "Expected IO error, but the following value was produced: "
      ++ showValue x

-------------------------------------------------------------------------------
-- Instance for the reporter monad                                           --
-------------------------------------------------------------------------------

-- | Utility function that print the given message like an item of an
--   unordered Markdown list.
showListItem :: String -> String
showListItem = (++ "\n") . (" * " ++) . intercalate "\n   " . lines

-- | Converts the pretty printing function for the result of a reporter to
--   a pretty printing function for the result of 'runReporterT'.
showReporterValue :: (a -> String) -> (Maybe a, [Message]) -> String
showReporterValue showValue (mx, ms) =
  "Reporter result where:\n"
    ++ showReportedValue showValue mx
    ++ showReportedMessages ms

-- | Converts the pretty printing function for the result of a reporter to
--   a pretty printing function for the value in an error message in an
--   exception.
showReportedValue :: (a -> String) -> Maybe a -> String
showReportedValue _ Nothing = "No value was produced."
showReportedValue showValue (Just x) =
  showListItem $ "The following value was produced: " ++ showValue x

-- | Pretty prints the messages that were reported by a reporter for an
--   error message in an expectation.
showReportedMessages :: [Message] -> String
showReportedMessages [] = showListItem $ "No messages were reported."
showReportedMessages [m] =
  showListItem $ "The following message was reported:\n" ++ showPretty m
showReportedMessages ms =
  showListItem
    $  "The following "
    ++ show (length ms)
    ++ " messages were reported:\n"
    ++ showPretty ms

-- | A reporter fails when a fatal message is reported.
instance MonadTestable m err => MonadTestable (ReporterT m) [Message] where
  shouldReturnWith' showValue reporter setExpectation =
    shouldReturnWith' (showReporterValue showValue) (runReporterT reporter)
      $ \result -> case result of
          (Just x, _) -> setExpectation x
          (Nothing, ms) ->
            assertFailure
              $  "Unexpected fatal message.\n"
              ++ showReportedMessages ms
  shouldFailWith' showValue reporter setExpectation =
    shouldReturnWith' (showReporterValue showValue) (runReporterT reporter)
      $ \result -> case result of
          (Nothing, ms) -> setExpectation ms
          (Just x, ms)
            | null ms
            -> assertFailure
              $  "Expected a fatal message, but no messages were reported.\n"
              ++ showReportedValue showValue (Just x)
            | otherwise
            -> assertFailure
              $  "Expected a fatal message to be reported, but got none.\n"
              ++ showReportedValue showValue (Just x)
              ++ showReportedMessages ms

-------------------------------------------------------------------------------
-- Instance for the converter monad                                          --
-------------------------------------------------------------------------------

-- | Initializes the test environment for the converter monad.
initTestEnvironment :: IO Environment
initTestEnvironment = do
  (maybeEnv, ms) <- runReporterT $ do
    preludeIface    <- loadTestModuleInterface "./base/Prelude.toml"
    quickCheckIface <- loadTestModuleInterface "./base/Test/QuickCheck.toml"
    return
      $ foldr makeModuleAvailable emptyEnv
      $ [preludeIface, quickCheckIface]
  case maybeEnv of
    Just env -> return env
    Nothing ->
      assertFailure
        $  "Could not initialize test environment.\n"
        ++ showReportedMessages ms

-- | A global variable that caches the module interfaces that are part of
--   the initial test environment (see 'initTestEnvironment') such that
--   they do not have to be loaded in every test case.
{-# NOINLINE moduleInterfaceCache #-}
moduleInterfaceCache :: IORef [(HS.ModName, ModuleInterface)]
moduleInterfaceCache = unsafePerformIO $ newIORef []

-- | Loads the module interface file for the module with the given name from
--   the base library.
--
--   If the module interface has been loaded before, the previously loaded
--   interface file is restored from 'moduleInterfaceCache'.
loadTestModuleInterface
  :: (MonadIO r, MonadReporter r) => FilePath -> r ModuleInterface
loadTestModuleInterface ifaceFile = do
  cache <- liftIO $ readIORef moduleInterfaceCache
  case lookup ifaceFile cache of
    Nothing -> do
      iface <- loadModuleInterface ifaceFile
      let cache' = (ifaceFile, iface) : cache
      liftIO $ writeIORef moduleInterfaceCache cache'
      return iface
    Just iface -> return iface

-- | A converter is evaluated within the test environment created by
--   'initTestEnvironment' and the resulting reporter is handled by
--   the 'MonadTestable' instance for 'ReporterT'.
instance MonadTestable m err => MonadTestable (ConverterT m) [Message] where
  shouldReturnWith' showValue converter setExpectation = do
    env <- initTestEnvironment
    shouldReturnWith' showValue (evalConverterT converter env) setExpectation
  shouldFailWith' showValue converter setExpectation = do
    env <- initTestEnvironment
    shouldFailWith' showValue (evalConverterT converter env) setExpectation

-------------------------------------------------------------------------------
-- QuickCheck                                                                --
-------------------------------------------------------------------------------

-- | Sets the expectation that the given computation returns a testable
--   QuickCheck property and returns a property that is satisfied if and
--   only if.
shouldReturnProperty
  :: (MonadTestable m err, Testable prop) => m prop -> Property
shouldReturnProperty mp =
  idempotentIOProperty $ shouldReturnWith' (const "<property>") mp return
