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
-- Reporter and converter moands                                             --
-------------------------------------------------------------------------------

-- | Gets the expectation produced by the given reported and expects that
--   the reporter does not report a fatal message.
fromReporter :: Reporter Expectation -> Expectation
fromReporter reporter = foldReporter reporter id failure
 where
    -- | If the reporter reported a fatal message, the test fails and prints
    --   the reported messages.
  failure :: Expectation
  failure = expectationFailure (showPretty (messages reporter))

-- | Evaluates the given converter in the default environment. Returns the
--   expectation produced by the converter and expects that no fatal message
--   is reported.
fromConverter :: Converter Expectation -> Expectation
fromConverter = fromReporter . flip evalConverter defaultEnvironment

-------------------------------------------------------------------------------
-- Parsing and simplification                                                --
-------------------------------------------------------------------------------

-- | Parses and simplifies a Haskell type for testing purposes.
parseTestType :: String -> Converter HS.Type
parseTestType input =
  liftReporter (parseType "<test-input>" input >>= simplifyType)

-------------------------------------------------------------------------------
-- Conversion                                                                --
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
