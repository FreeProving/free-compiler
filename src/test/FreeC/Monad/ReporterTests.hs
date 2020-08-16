-- | This module contains tests for the 'Reporter' monad.
module FreeC.Monad.ReporterTests ( testReporter ) where

import           System.IO.Error      ( ioError, userError )
import           Test.Hspec

import           FreeC.IR.SrcSpan
import           FreeC.Monad.Reporter

-- | Test group for all "FreeC.Monad.Reporter" tests.
testReporter :: Spec
testReporter = describe "FreeC.Monad.Reporter" $ do
  testRunReporter
  testIsFatal
  testMessages
  testLiftIO

-------------------------------------------------------------------------------
-- Tests for @runReporter@                                                  --
-------------------------------------------------------------------------------
-- | Test group for 'runReporter' tests.
testRunReporter :: Spec
testRunReporter = describe "runReporter" $ do
  it "returns 'Just' the produced value if no message was reported" $ do
    runReporter (return testValue) `shouldBe` (Just testValue, [])
  it "returns 'Just' the produced value if no fatal message was reported" $ do
    runReporter (report testMessage1 >> return testValue)
      `shouldBe` (Just testValue, [testMessage1])
  it "returns 'Nothing' if a fatal message was reported" $ do
    runReporter (reportFatal testMessage1)
      `shouldBe` (Nothing :: Maybe (), [testMessage1])

-------------------------------------------------------------------------------
-- Test data                                                                 --
-------------------------------------------------------------------------------
-- | A message that is reported by some reporters for testing purposes.
testMessage1 :: Message
testMessage1 = Message NoSrcSpan Error "Keyboard not found\nPress F1 to Resume"

-- | A message that is reported by some reporters for testing purposes.
testMessage2 :: Message
testMessage2 = Message NoSrcSpan Error "Maximum call stack size exceeded!"

-- | A value that is returned by some reporters for testing purposes.
testValue :: Int
testValue = 42

-------------------------------------------------------------------------------
-- Tests for @isFatal@                                                       --
-------------------------------------------------------------------------------
-- | Test group for 'isFatal' tests.
testIsFatal :: Spec
testIsFatal = describe "isFatal" $ do
  it "is not fatal to return from a reporter" $ do
    isFatal (return testValue) `shouldBe` False
  it "is not fatal to report a regular message" $ do
    isFatal (report testMessage1) `shouldBe` False
  it "is fatal to report a fatal message" $ do
    isFatal (reportFatal testMessage1) `shouldBe` True
  it "is fatal if a computation involves reporting a fatal message" $ do
    isFatal (reportFatal testMessage1 >> return testValue) `shouldBe` True

-------------------------------------------------------------------------------
-- Tests for @messages@                                                      --
-------------------------------------------------------------------------------
-- | Test group for 'messages' tests.
testMessages :: Spec
testMessages = describe "messages" $ do
  it "collects all reported messages" $ do
    let reporter = report testMessage1 >> report testMessage1
    length (messages reporter) `shouldBe` 2
  it "collects all messages reported before a fatal message" $ do
    let reporter = report testMessage1 >> reportFatal testMessage1
    length (messages reporter) `shouldBe` 2
  it "collects no messages reported after a fatal messages" $ do
    let reporter = reportFatal testMessage1 >> report testMessage1
    length (messages reporter) `shouldBe` 1
  it "collects no messages in the right order" $ do
    let reporter = report testMessage1 >> report testMessage2
    messages reporter `shouldBe` [testMessage1, testMessage2]

-------------------------------------------------------------------------------
-- Tests for @liftIO@                                                        --
-------------------------------------------------------------------------------
-- | Test group for 'liftIO' tests.
testLiftIO :: Spec
testLiftIO = describe "liftIO reports IO errors" $ do
  it "catches IO errors" $ do
    reporter <- unhoist $ liftIO $ ioError (userError "catch me")
    isFatal reporter `shouldBe` True
    length (messages reporter) `shouldBe` 1
  it "forwards result" $ do
    reporter <- unhoist $ liftIO (return ())
    isFatal reporter `shouldBe` False
    length (messages reporter) `shouldBe` 0
