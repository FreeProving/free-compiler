-- | This module contains utility functions for testing the compiler.

module Compiler.Util.Test where

import           Test.Hspec

import           Compiler.MyConverter
import           Compiler.Converter.State
import           Compiler.Language.Haskell.Parser
import           Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.Language.Haskell.Simplifier
import           Compiler.Pretty
import           Compiler.Pretty.Coq            ( )
import           Compiler.Reporter

-------------------------------------------------------------------------------
-- Evaluation of converters                                                  --
-------------------------------------------------------------------------------

-- | Evaluates the given converter in the default environment.
fromConverter :: Converter a -> Reporter a
fromConverter = flip evalConverter defaultEnvironment

-------------------------------------------------------------------------------
-- Expectations for reports                                                  --
-------------------------------------------------------------------------------

-- | Sets the expectation that no fatal message is reported by the given
--   reporter. If no fatal message is reported, the expectations set by the
--   reporter are returned. Otherwise the reported messages are printed.
shouldSucceed :: Reporter Expectation -> Expectation
shouldSucceed reporter = foldReporter reporter id failure
 where
  failure :: Expectation
  failure = expectationFailure (showPretty (messages reporter))

-- | Sets the expectation that a fatal messages is reported by the given
--   reporter. Prints the produced value and reported messages otherwise.
shouldReportFatal :: Show a => Reporter a -> Expectation
shouldReportFatal reporter = foldReporter reporter
                                          unexpectedSuccess
                                          expectedFailure
 where
  expectedFailure :: Expectation
  expectedFailure = return ()

  unexpectedSuccess :: Show a => a -> Expectation
  unexpectedSuccess value =
    expectationFailure
      $  "Expected a fatal message to be reported. Got "
      ++ show (length (messages reporter))
      ++ " messages, none of which is fatal."
      ++ "\n\nThe following value was produced:"
      ++ show value
      ++ "\n\nThe following messages where reported:"
      ++ show value
      ++ showPretty (messages reporter)

-------------------------------------------------------------------------------
-- Parsing and simplification utility functions                              --
-------------------------------------------------------------------------------

-- | Parses and simplifies a Haskell type for testing purposes.
parseTestType :: String -> Converter HS.Type
parseTestType input =
  liftReporter (parseType "<test-input>" input >>= simplifyType)

-------------------------------------------------------------------------------
-- Conversion expectations                                                   --
-------------------------------------------------------------------------------

-- | Translates the string representation of a Haskell type to Coq and expects
--   the result to be the given sting representation of a Coq type.
shouldTranslateTypeTo
  :: String -- ^ The input Haskell type.
  -> String -- ^ The expected output Coq type.
  -> Converter Expectation
shouldTranslateTypeTo input expectedOutput = do
  hsType  <- parseTestType input
  coqType <- convertType hsType
  return ((showPretty coqType) `shouldBe` expectedOutput)
