-- | This module contains utility functions for testing the compiler.

module Compiler.Util.Test where

import           Test.Hspec

import           Data.Maybe                     ( catMaybes )

import           Compiler.Converter
import           Compiler.Converter.State
import           Compiler.Language.Coq.AST     as G
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
    ++ " messages were reported:\n"
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
      ++ "\n\nThe following messages were reported:"
      ++ showPretty ms

-------------------------------------------------------------------------------
-- Parsing and simplification utility functions                              --
-------------------------------------------------------------------------------

-- | Parses and simplifies a Haskell type for testing purposes.
parseTestType :: String -> Simplifier HS.Type
parseTestType input =
  liftReporter (parseType "<test-input>" input) >>= simplifyType

-- | Parses and simplifies a Haskell type for testing purposes.
parseTestExpr :: String -> Simplifier HS.Expr
parseTestExpr input =
  liftReporter (parseExpr "<test-input>" input) >>= simplifyExpr

-- | Parses and simplifies a Haskell declaration for testing purposes.
parseTestDecl :: String -> Simplifier (Maybe HS.Decl)
parseTestDecl input =
  liftReporter (parseDecl "<test-input>" input) >>= simplifyDecl

-- | Parses and simplifies Haskell declarations for testing purposes.
parseTestDecls :: [String] -> Simplifier [HS.Decl]
parseTestDecls input = mapM parseTestDecl input >>= return . catMaybes

-------------------------------------------------------------------------------
-- Conversion utility functions                                              --
-------------------------------------------------------------------------------

-- | Parses, simplifies and converts a Haskell type for testing purposes.
convertTestType :: String -> Converter G.Term
convertTestType input = parseTestType input >>= convertType

-- | Parses, simplifies and converts a Haskell expression for testing purposes.
convertTestExpr :: String -> Converter G.Term
convertTestExpr input = parseTestExpr input >>= convertExpr

-- | Parses, simplifies and converts a Haskell declaration for testing purposes.
convertTestDecl :: String -> Converter [G.Sentence]
convertTestDecl = convertTestDecls . return

-- | Parses, simplifies and converts a Haskell declarations for testing
--   purposes.
convertTestDecls :: [String] -> Converter [G.Sentence]
convertTestDecls input = parseTestDecls input >>= convertDecls

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
  coqType <- convertTestType input
  return
    (          discardWhitespace (showPretty coqType)
    `shouldBe` discardWhitespace expectedOutput
    )

-- | Translates the string representation of a Haskell expression to Coq and
--   sets the expectation that the result equals the given sting representation
--   of a Coq expression term.
shouldTranslateExprTo
  :: String -- ^ The input Haskell expression.
  -> String -- ^ The expected output Coq expression.
  -> Converter Expectation
shouldTranslateExprTo input expectedOutput = do
  coqExpr <- convertTestExpr input
  return
    (          discardWhitespace (showPretty coqExpr)
    `shouldBe` discardWhitespace expectedOutput
    )

-- | Translates the string representation of a Haskell declaration to Coq and
--   sets the expectation that the result equals the given Gallina sentences.
--
--   Whitespace in the actual and expected output does not have to match.
shouldTranslateDeclsTo :: [String] -> String -> Converter Expectation
shouldTranslateDeclsTo input expectedOutput = do
  coqDecls <- convertTestDecls input
  return
    $          discardWhitespace (showPretty coqDecls)
    `shouldBe` discardWhitespace expectedOutput


-------------------------------------------------------------------------------
-- Utility functions                                                        --
-------------------------------------------------------------------------------

-- | Replaces all whitespace in the given string by a single space.
discardWhitespace :: String -> String
discardWhitespace = unwords . words
