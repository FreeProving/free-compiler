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
shouldSucceed reporter = case runReporter reporter of
  (Just x , _ ) -> x
  (Nothing, ms) -> expectationFailure
    (  "The following "
    ++ show (length ms)
    ++ " messages where reported:"
    ++ showPretty ms
    )

-- | Sets the expectation that a fatal messages is reported by the given
--   reporter. Prints the produced value and reported messages otherwise.
shouldReportFatal :: Show a => Reporter a -> Expectation
shouldReportFatal reporter = case runReporter reporter of
  (Nothing, _) -> return ()
  (Just x, ms) ->
    expectationFailure
      $  "Expected a fatal message to be reported. Got "
      ++ show (length ms)
      ++ " messages, none of which is fatal."
      ++ "\n\nThe following value was produced:"
      ++ show x
      ++ "\n\nThe following messages where reported:"
      ++ showPretty ms

-------------------------------------------------------------------------------
-- Parsing and simplification utility functions                              --
-------------------------------------------------------------------------------

-- | Parses and simplifies a Haskell type for testing purposes.
parseTestType :: String -> Converter HS.Type
parseTestType input =
  liftReporter (parseType "<test-input>" input >>= simplifyType)

-- | Parses and simplifies a Haskell declaration for testing purposes.
parseTestDecl :: String -> Converter HS.Decl
parseTestDecl input =
  liftReporter (parseDecl "<test-input>" input >>= simplifyDecl)

-------------------------------------------------------------------------------
-- Conversion expectations                                                   --
-------------------------------------------------------------------------------

-- | Translates the string representation of a Haskell type to Coq and sets the
--   expectation that the result equals the given sting representation of a Coq
--   type term.
shouldTranslateTypeTo
  :: String -- ^ The input Haskell type.
  -> String -- ^ The expected output Coq type.
  -> Converter Expectation
shouldTranslateTypeTo input expectedOutput = do
  hsType  <- parseTestType input
  coqType <- convertType hsType
  return ((showPretty coqType) `shouldBe` expectedOutput)

-- | Translate sthe string representation of a Haskell declaration to Coq and
--   sets the expectation that the result equals the given Gallina sentences.
--
--   Whitespace in the actual and expected output does not have to match.
shouldTranslateDeclsTo :: String -> String -> Converter Expectation
shouldTranslateDeclsTo input expectedOutput = do
  hsDecl   <- parseTestDecl input
  coqDecls <- convertDecls [hsDecl]
  return
    $          discardWhitespace (showPretty coqDecls)
    `shouldBe` discardWhitespace expectedOutput


-------------------------------------------------------------------------------
-- Utility functions                                                        --
-------------------------------------------------------------------------------

-- | Replaces all whitespace in the given string by a single space.
discardWhitespace :: String -> String
discardWhitespace = unwords . words
