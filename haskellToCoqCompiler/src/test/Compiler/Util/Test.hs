-- | This module contains utility functions for testing the compiler.

module Compiler.Util.Test where

import           Test.Hspec

import           Data.Maybe                     ( catMaybes )

import           Compiler.Converter
import qualified Compiler.Coq.AST              as G
import           Compiler.Coq.Pretty            ( )
import           Compiler.Environment.Loader
import           Compiler.Environment.Renamer
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Parser
import           Compiler.Haskell.Simplifier
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Evaluation of converters                                                  --
-------------------------------------------------------------------------------

-- | Evaluates the given converter in the default environment.
fromConverter :: Converter a -> ReporterIO a
fromConverter converter = do
  env <- loadEnvironment "base/env.toml"
  hoist $ evalConverter converter env

-------------------------------------------------------------------------------
-- Expectations for reports                                                  --
-------------------------------------------------------------------------------

-- | Sets the expectation that no fatal message is reported by the given
--   reporter. If no fatal message is reported, the expectations set by the
--   reporter are returned. Otherwise the reported messages are printed.
shouldSucceed :: ReporterIO Expectation -> Expectation
shouldSucceed reporter = do
  result <- runReporterT reporter
  case result of
    (Just x , _ ) -> x
    (Nothing, ms) -> expectationFailure
      (  "The following "
      ++ show (length ms)
      ++ " messages were reported:\n"
      ++ showPretty ms
      )

-- | Sets the expectation that a fatal messages is reported by the given
--   reporter. Prints the produced value and reported messages otherwise.
shouldReportFatal :: Show a => ReporterIO a -> Expectation
shouldReportFatal reporter = do
  result <- runReporterT reporter
  case result of
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
-- Defining test idenifiers                                                  --
-------------------------------------------------------------------------------

-- | Alias for 'renameAndDefineTypeCon'.
defineTestTypeCon :: String -> Int -> Converter String
defineTestTypeCon = renameAndDefineTypeCon

-- | Alias for 'renameAndDefineTypeVar'.
defineTestTypeVar :: String -> Converter String
defineTestTypeVar = renameAndDefineTypeVar

-- | Like 'renameAndDefineCon' but the argument and return types are parsed
--   from the given string.
defineTestCon :: String -> Int -> String -> Converter (String, String)
defineTestCon ident arity typeStr = do
  typeExpr <- parseTestType typeStr
  let (argTypes, returnType) = HS.splitType typeExpr arity
  renameAndDefineCon ident argTypes returnType

  -- | Alias for 'defineTestVar'.
defineTestVar :: String -> Converter String
defineTestVar = renameAndDefineVar

-- | Like 'renameAndDefineFunc' but the argument and return types are parsed from
--   the given string.
defineTestFunc :: String -> Int -> String -> Converter String
defineTestFunc ident arity typeStr = do
  typeExpr <- parseTestType typeStr
  let (argTypes, returnType) = HS.splitType typeExpr arity
  renameAndDefineFunc ident argTypes returnType

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
