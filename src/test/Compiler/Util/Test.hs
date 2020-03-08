{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains utility functions for testing the compiler.

module Compiler.Util.Test where

import           Test.Hspec
import           Test.QuickCheck

import           Control.Exception
import           Control.Monad                  ( replicateM )
import           Data.IORef                     ( IORef
                                                , newIORef
                                                , readIORef
                                                , writeIORef
                                                )
import           Data.Maybe                     ( catMaybes
                                                , fromJust
                                                )
import           System.IO.Unsafe               ( unsafePerformIO )

import           Compiler.Analysis.DependencyExtraction
                                                ( typeVars )
import           Compiler.Analysis.TypeInference
import           Compiler.Converter
import qualified Compiler.Coq.AST              as G
import           Compiler.Coq.Pretty
import           Compiler.Environment
import           Compiler.Environment.Decoder
import           Compiler.Environment.Entry
import           Compiler.Environment.Importer
import           Compiler.Environment.Renamer
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Parser
import           Compiler.Haskell.Simplifier
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Arbitrary instances                                                       --
-------------------------------------------------------------------------------

-- | Generates an arbitrary type expression.
instance Arbitrary HS.Type where
  arbitrary = oneof
    [arbitraryTypeVar, arbitraryTypeConApp, arbitraryFuncType]
   where
    arbitraryTypeVar :: Gen HS.Type
    arbitraryTypeVar = do
      ident <- oneof $ map return ["a", "b", "c", "d"]
      return (HS.TypeVar NoSrcSpan ident)

    arbitraryTypeConApp :: Gen HS.Type
    arbitraryTypeConApp = do
      (name, arity) <- oneof $ map
        return
        [ (HS.boolTypeConName   , 0)
        , (HS.integerTypeConName, 0)
        , (HS.unitTypeConName   , 0)
        , (HS.listTypeConName   , 1)
        , (HS.tupleTypeConName 2, 2)
        ]
      args <- replicateM arity arbitrary
      return (HS.typeConApp NoSrcSpan name args)

    arbitraryFuncType :: Gen HS.Type
    arbitraryFuncType = HS.TypeFunc NoSrcSpan <$> arbitrary <*> arbitrary

-------------------------------------------------------------------------------
-- Evaluation of converters and reporters                                    --
-------------------------------------------------------------------------------

-- | Evaluates the given converter in the default environment.
--
--   The @Prelude@ module is imported first.
fromConverter :: Converter a -> ReporterIO a
fromConverter converter = fromModuleConverter $ do
  Just preludeIface <- inEnv $ lookupAvailableModule HS.preludeModuleName
  modifyEnv $ importInterface preludeIface
  modifyEnv $ importInterfaceAs HS.preludeModuleName preludeIface
  converter

-- | Like 'fromConverter' but the @Prelude@ module is not imported
--   automatically such that Haskell modules can be converted in the
--   given converter.
fromModuleConverter :: Converter a -> ReporterIO a
fromModuleConverter converter = flip evalConverterT emptyEnv $ do
  makeTestModuleAvailable "./base/Prelude.toml"
  makeTestModuleAvailable "./base/Test/QuickCheck.toml"
  hoist converter

-- | A global variable that caches the module interface of the @Prelude@
--   module such that it does not have to be loaded in every test case.
moduleInterfaceCache :: IORef [(HS.ModName, ModuleInterface)]
moduleInterfaceCache = unsafePerformIO $ newIORef []

-- | Loads the module interface file for the module with the given name from
--   the base library.
--
--   If the module interface has been loaded before, the previously loaded
--   interface file is restored from 'moduleInterfaceCache'.
loadTestModuleInterface :: FilePath -> ReporterIO ModuleInterface
loadTestModuleInterface ifaceFile = do
  cache <- lift $ readIORef moduleInterfaceCache
  case lookup ifaceFile cache of
    Nothing -> do
      iface <- loadModuleInterface ifaceFile
      let cache' = (ifaceFile, iface) : cache
      lift $ writeIORef moduleInterfaceCache cache'
      return iface
    Just iface -> return iface

-- | Loads the given module interface filw using 'loadTestModuleInterface'
--   and adds it to the environment.
makeTestModuleAvailable :: FilePath -> ConverterIO ()
makeTestModuleAvailable ifaceFile = do
  iface <- lift' $ loadTestModuleInterface ifaceFile
  modifyEnv $ makeModuleAvailable iface

-- | Evaluates the given reporter and throws an IO exception when a fatal
--   error message is reported.
fromReporter :: ReporterIO a -> IO a
fromReporter reporter = do
  result <- runReporterT reporter
  case result of
    (Just x , _ ) -> return x
    (Nothing, ms) -> throwIO $ userError
      (  "The following "
      ++ show (length ms)
      ++ " messages were reported:\n"
      ++ showPretty ms
      )

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
-- QuickCheck properties for converters                                      --
-------------------------------------------------------------------------------

-- | Converts the given reporter to a QuickCheck property that is fullfilled
--   if and only if the given reporter does not report a fatal error and
--   the returned testable property is satisfied.
shouldSucceedProperty :: Testable prop => ReporterIO prop -> Property
shouldSucceedProperty reporter = idempotentIOProperty $ do
  result <- runReporterT reporter
  case result of
    (Nothing, ms) -> return $ counterexample
      (  "The following "
      ++ show (length ms)
      ++ " messages were reported:\n"
      ++ showPretty ms
      )
      (property Discard)
    (Just prop, _) -> return (property prop)

-------------------------------------------------------------------------------
-- Parsing and simplification utility functions                              --
-------------------------------------------------------------------------------

-- | Parses and simplifies a Haskell type for testing purposes.
parseTestType :: String -> Simplifier HS.Type
parseTestType input =
  liftReporter (parseType "<test-input>" input) >>= simplifyType

-- | Parses and simplifies a Haskell type and abstracts it into a type schema
--   for testing purposes.
--
--   If there is a @forall@ quantifier, only the specified type arguments
--   are abstracted away.
parseTestTypeSchema :: String -> Simplifier HS.TypeSchema
parseTestTypeSchema input =
  liftReporter (parseTypeSchema "<test-input>" input) >>= simplifyTypeSchema

-- | Parses and simplifies a Haskell type for testing purposes.
parseTestExpr :: String -> Simplifier HS.Expr
parseTestExpr input =
  liftReporter (parseExpr "<test-input>" input) >>= simplifyExpr

-- | Parses and simplifies Haskell declarations for testing purposes.
parseTestDecls
  :: [String] -> Simplifier ([HS.TypeDecl], [HS.TypeSig], [HS.FuncDecl])
parseTestDecls input =
  liftReporter (mapM (parseDecl "<test-input>") input) >>= simplifyDecls

-- | Parses and simplifies a Haskell module for testing purposes.
parseTestModule :: [String] -> Simplifier HS.Module
parseTestModule input =
  liftReporter (parseModuleWithComments "<test-input>" (unlines input))
    >>= uncurry simplifyModuleWithComments

-------------------------------------------------------------------------------
-- Configuring the environment                                               --
-------------------------------------------------------------------------------

-- | Setup the environment as if a module with the given name is being
--   translated.
enterTestModule :: String -> Converter ()
enterTestModule modName = modifyEnv $ \env -> env { envModName = modName }

-------------------------------------------------------------------------------
-- Defining test idenifiers                                                  --
-------------------------------------------------------------------------------

-- | Adds the given entry to the current environment and renames it such that
--   no name conflict occurs.
--
--   Returns the Coq identifier assigned to the entry by the renamer.
renameAndAddTestEntry :: EnvEntry -> Converter String
renameAndAddTestEntry =
  fmap (fromJust . G.unpackQualid . entryIdent) . renameAndAddEntry

-- | Defines a type constructor for testing purposes.
--
--   Returns the Coq identifier assigned to the type constructor.
defineTestTypeCon :: String -> Int -> Converter String
defineTestTypeCon ident arity = renameAndAddTestEntry DataEntry
  { entrySrcSpan = NoSrcSpan
  , entryArity   = arity
  , entryName    = HS.UnQual (HS.Ident ident)
  , entryIdent   = undefined -- filled by renamer
  }

-- | Defines a type synonym for testing purposes.
--
--   Returns the Coq identifier assigned to the type synonym.
defineTestTypeSyn :: String -> [String] -> String -> Converter String
defineTestTypeSyn ident typeArgs typeStr = do
  typeExpr <- parseTestType typeStr
  renameAndAddTestEntry TypeSynEntry
    { entrySrcSpan  = NoSrcSpan
    , entryArity    = length typeArgs
    , entryTypeArgs = typeArgs
    , entryTypeSyn  = typeExpr
    , entryName     = HS.UnQual (HS.Ident ident)
    , entryIdent    = undefined -- filled by renamer
    }

-- | Defines a type variable 'renameAndDefineTypeVar' for testing purposes.
--
--   Returns the Coq identifier assigned to the type variable.
defineTestTypeVar :: String -> Converter String
defineTestTypeVar ident = renameAndAddTestEntry TypeVarEntry
  { entrySrcSpan = NoSrcSpan
  , entryName    = HS.UnQual (HS.Ident ident)
  , entryIdent   = undefined -- filled by renamer
  }

-- | Adds an entry for a data constructor for testing purposes.
--
--   The argument and return types are parsed from the given string.
--   Returns the Coq identifier assigned to the data constructor.
defineTestCon :: String -> Int -> String -> Converter (String, String)
defineTestCon ident arity typeStr = do
  typeExpr <- parseTestType typeStr
  let (argTypes, returnType) = HS.splitType typeExpr arity
  entry <- renameAndAddEntry ConEntry
    { entrySrcSpan    = NoSrcSpan
    , entryArity      = arity
    , entryTypeArgs   = maybe []
                              (catMaybes . map HS.identFromQName . typeVars)
                              returnType
    , entryArgTypes   = argTypes
    , entryReturnType = returnType
    , entryName       = HS.UnQual (HS.Ident ident)
    , entryIdent      = undefined -- filled by renamer
    , entrySmartIdent = undefined -- filled by renamer
    }
  let (Just ident'     ) = G.unpackQualid (entryIdent entry)
      (Just smartIdent') = G.unpackQualid (entrySmartIdent entry)
  return (ident', smartIdent')

-- | Defines a variable for testing purposes.

--   Returns the Coq identifier assigned to the function.
defineTestVar :: String -> Converter String
defineTestVar ident = renameAndAddTestEntry VarEntry
  { entrySrcSpan = NoSrcSpan
  , entryIsPure  = False
  , entryName    = HS.UnQual (HS.Ident ident)
  , entryIdent   = undefined -- filled by renamer
  }

-- | Adds an entry for a function declaration for testing purposes.
--
--   The argument and return types are parsed from the given string.
--   Returns the Coq identifier assigned to the function.
defineTestFunc :: String -> Int -> String -> Converter String
defineTestFunc =
  defineTestFunc' False

-- | Like 'defineTestFunc' but the first argument controls whether the
--   defined function is partial or not.
defineTestFunc'
  :: Bool -> String -> Int -> String -> Converter String
defineTestFunc' partial ident arity typeStr = do
  HS.TypeSchema _ typeArgs typeExpr <- parseTestTypeSchema typeStr
  let (argTypes, returnType) = HS.splitType typeExpr arity
  renameAndAddTestEntry FuncEntry
    { entrySrcSpan       = NoSrcSpan
    , entryArity         = arity
    , entryTypeArgs      = map HS.fromDeclIdent typeArgs
    , entryArgTypes      = argTypes
    , entryReturnType    = returnType
    , entryNeedsFreeArgs = True
    , entryIsPartial     = partial
    , entryName          = HS.UnQual (HS.Ident ident)
    , entryIdent         = undefined -- filled by renamer
    }

-- | Like 'defineTestFunc' but also marks the given function as partial.
--
--   Returns the Coq identifier assigned to the function.
definePartialTestFunc :: String -> Int -> String -> Converter String
definePartialTestFunc =
  defineTestFunc' True

-------------------------------------------------------------------------------
-- Conversion utility functions                                              --
-------------------------------------------------------------------------------

-- | Parses, simplifies and converts a Haskell type for testing purposes.
convertTestType :: String -> Converter G.Term
convertTestType input = parseTestType input >>= convertType

-- | Parses, simplifies and converts a Haskell expression for testing purposes.
convertTestExpr :: String -> Converter G.Term
convertTestExpr input =
  parseTestExpr input >>= annotateExprTypes >>= convertExpr

-- | Parses, simplifies and converts a Haskell declaration for testing purposes.
convertTestDecl :: String -> Converter [G.Sentence]
convertTestDecl = convertTestDecls . return

-- | Parses, simplifies and converts a Haskell declarations for testing
--   purposes.
convertTestDecls :: [String] -> Converter [G.Sentence]
convertTestDecls input = do
  (typeDecls, typeSigs, funcDecls) <- parseTestDecls input
  convertDecls typeDecls typeSigs funcDecls

-- | Parses, simplifies and converts a Haskell module for testing purposes.
convertTestModule :: [String] -> Converter [G.Sentence]
convertTestModule input = do
  haskellAst <- parseTestModule input
  convertModule haskellAst

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
  return (PrettyCoq coqType `prettyShouldBe` expectedOutput)

-- | Translates the string representation of a Haskell expression to Coq and
--   sets the expectation that the result equals the given sting representation
--   of a Coq expression term.
shouldTranslateExprTo
  :: String -- ^ The input Haskell expression.
  -> String -- ^ The expected output Coq expression.
  -> Converter Expectation
shouldTranslateExprTo input expectedOutput = do
  coqExpr <- convertTestExpr input
  return (PrettyCoq coqExpr `prettyShouldBe` expectedOutput)

-- | Translates the string representation of Haskell declarations to Coq and
--   sets the expectation that the result equals the given Gallina sentences.
--
--   Whitespace in the actual and expected output does not have to match.
shouldTranslateDeclsTo :: [String] -> String -> Converter Expectation
shouldTranslateDeclsTo input expectedOutput = do
  coqDecls <- convertTestDecls input
  return (map PrettyCoq coqDecls `prettyShouldBe` expectedOutput)

-- | Converts the string representation of a Haskell module to Coq and sets
--   the expectation that the result equals the given Gallina Sentences.
--
--   Whitespace in the actual and expected output does not have to match.
shouldTranslateModuleTo :: [String] -> [String] -> Converter Expectation
shouldTranslateModuleTo input expectedOutputLines = do
  coqAst <- convertTestModule input
  let expectedOutput = unlines expectedOutputLines
  return (map PrettyCoq coqAst `prettyShouldBe` expectedOutput)

-------------------------------------------------------------------------------
-- Utility functions                                                        --
-------------------------------------------------------------------------------

-- | Pretty prints the given value and sets the expectation that the result
--   equals the given string.
--
--   Whitespace is ignored (see 'discardWhitespace').
prettyShouldBe :: (Pretty a, Pretty b) => a -> b -> Expectation
prettyShouldBe input expectedOutput = discardWhitespace (showPretty input)
  `shouldBe` discardWhitespace (showPretty expectedOutput)

-- | Replaces all whitespace in the given string by a single space.
discardWhitespace :: String -> String
discardWhitespace = unwords . words