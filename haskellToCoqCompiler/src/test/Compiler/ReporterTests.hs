module Compiler.ReporterTests
  ( testReporter
  )
where

import           System.IO.Error                ( ioError
                                                , userError
                                                )

import           Test.Hspec

import           Compiler.Reporter

-- | Test group for all @Compiler.Reporter@ tests.
testReporter :: Spec
testReporter = describe "Compiler.Reporter" $ do
  testIsFatal
  testMessages
  testFoldReporter
  testReportIOErrors

-------------------------------------------------------------------------------
-- Test data                                                                 --
-------------------------------------------------------------------------------

-- | A message that is reported by some reporters for testing purposes.
testMessage :: Message
testMessage = Message Nothing Error "Keyboard not found\nPress F1 to Resume"

-- | A value that is returned some reporters for testing purposes.
testValue1 :: Int
testValue1 = 42

-- | An alternative value that is returned some reporters for testing purposes.
testValue2 :: Int
testValue2 = 1337

-------------------------------------------------------------------------------
-- Tests for @isFatal@                                                       --
-------------------------------------------------------------------------------

-- | Test group for 'isFatal' tests.
testIsFatal :: Spec
testIsFatal = describe "isFatal" $ do
  it "is not fatal to return from a reporter" $ do
    isFatal (return testValue1) `shouldBe` False
  it "is not fatal to report a regular message" $ do
    isFatal (report testMessage) `shouldBe` False
  it "is fatal to report a fatal message" $ do
    isFatal (reportFatal testMessage) `shouldBe` True
  it "is fatal if a computation involves reporting a fatal message" $ do
    isFatal (reportFatal testMessage >> return testValue1) `shouldBe` True

-------------------------------------------------------------------------------
-- Tests for @messages@                                                      --
-------------------------------------------------------------------------------

-- | Test group for 'messages' tests.
testMessages :: Spec
testMessages = describe "messages" $ do
  it "collects all reported messages" $ do
    let reporter = report testMessage >> report testMessage
    length (messages reporter) `shouldBe` 2
  it "collects all messages reported before a fatal message" $ do
    let reporter = report testMessage >> reportFatal testMessage
    length (messages reporter) `shouldBe` 2
  it "collects no messages reported after a fatal messages" $ do
    let reporter = reportFatal testMessage >> report testMessage
    length (messages reporter) `shouldBe` 1

-------------------------------------------------------------------------------
-- Tests for @foldReporter@                                                  --
-------------------------------------------------------------------------------

-- | Test group for 'foldReporter' tests.
testFoldReporter :: Spec
testFoldReporter = describe "testFoldReporter" $ do
  it "evaluates the first function if no fatal message was reported" $ do
    let reporter = return testValue1
    foldReporter reporter id testValue2 `shouldBe` testValue1
  it "return the second value if a fatal message was reported" $ do
    let reporter = reportFatal testMessage
    foldReporter reporter id testValue2 `shouldBe` testValue2


-------------------------------------------------------------------------------
-- Tests for @reportIOErrors@                                                --
-------------------------------------------------------------------------------

-- | Test group for 'reportIOErrors' tests.
testReportIOErrors :: Spec
testReportIOErrors = describe "reportIOErrors" $ do
  it "catches IO errors" $ do
    reporter <- reportIOErrors (ioError (userError "catch me"))
    isFatal reporter `shouldBe` True
    length (messages reporter) `shouldBe` 1
  it "forwards reported messages" $ do
    reporter <- reportIOErrors (return (report testMessage))
    isFatal reporter `shouldBe` False
    length (messages reporter) `shouldBe` 1
