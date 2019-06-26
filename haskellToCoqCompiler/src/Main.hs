module Main where

import           System.Environment             ( getArgs
                                                , getProgName
                                                )
import           System.Exit                    ( exitFailure )
import           System.Console.GetOpt
import           System.FilePath

import           Compiler.Converter             ( convertModuleWithPreamble )
import           Compiler.Language.Haskell.Parser
                                                ( parseModuleFile )
import qualified Compiler.Types

import           Compiler.Language.Coq.Pretty   ( )
import           Compiler.Pretty
import           Compiler.Reporter

-- | Data type that stores the command line options passed to the compiler.
data Options = Options
  {
    -- | Flag that indicates whether to show the usage information.
    optShowHelp :: Bool,

    -- | The input files passed to the compiler.
    --   All non-option command line arguments are considered input files.
    optInputFiles :: [FilePath],

    -- | The output directory or 'Nothing' if the output should be printed
    --   to @stdout@.
    optOutputDir :: Maybe FilePath,

    -- | The configured conversion monad.
    optConversionMonad :: Compiler.Types.ConversionMonad
  }

-- | The default command line options.
--
--   By default the @option@ monad is selected and output will be printed to
--   the console.
defaultOptions :: Options
defaultOptions = Options
  { optShowHelp        = False
  , optInputFiles      = []
  , optOutputDir       = Nothing
  , optConversionMonad = Compiler.Types.Option
  }

-- | Command line option descriptors from the @GetOpt@ library.
options :: [OptDescr (Options -> Options)]
options
  = [ Option ['h']
             ["help"]
             (NoArg (\opts -> opts { optShowHelp = True }))
             "Display this message."
    , Option
      ['o']
      ["output"]
      (ReqArg (\p opts -> opts { optOutputDir = Just p }) "DIR")
      (  "Path to output directory.\n"
      ++ "Optional. Prints to the console by default."
      )
    , Option
      ['m']
      ["monad"]
      (ReqArg
        (\m opts -> case m of
          "option"   -> opts { optConversionMonad = Compiler.Types.Option }
          "identity" -> opts { optConversionMonad = Compiler.Types.Identity }
        )
        "(option|identity)"
      )
      "Conversion monad.\nDefaults to \"option\"."
    ]

-- | The header of the help message.
--
--   This text is added before the description of the command line arguments.
usageHeader :: FilePath -> String
usageHeader progName =
  "Usage: "
    ++ progName
    ++ " [options...] <input-files...>\n\n"
    ++ "Command line options:"

-- | Prints the help message for the compiler.
--
--   The help message is displayed when the user specifies the "--help" option
--   or there are no input files.
putUsageInfo :: IO ()
putUsageInfo = do
  progName <- getProgName
  putStrLn (usageInfo (usageHeader progName) options)

-- | Parses the command line arguments.
--
--   If there are errors when parsing the command line arguments, a fatal
--   error message is reported.
--
--   All non-option arguments are considered as input files.
--
--   Returns the 'defaultOptions' if no arguments are specified.
parseArgs
  :: [String] -- ^ The command line arguments.
  -> Reporter Options
parseArgs args
  | null errors = return opts { optInputFiles = nonOpts }
  | otherwise = do
    mapM_ (report . Message Nothing Error) errors
    reportFatal $ Message
      Nothing
      Error
      (  "Failed to parse command line arguments.\n"
      ++ "Use '--help' for usage information."
      )
 where
  optSetters :: [Options -> Options]
  nonOpts :: [String]
  errors :: [String]
  (optSetters, nonOpts, errors) = getOpt Permute options args

  opts :: Options
  opts = foldr ($) defaultOptions optSetters

-- | The main function of the compiler.
--
--   Parses the command line arguments and invokes 'run' if successful.
main :: IO ()
main = do
  args <- getArgs
  let optReporter = parseArgs args
  putPretty (messages optReporter)
  foldReporter optReporter run exitFailure

-- | Handles the given command line options.
run :: Options -> IO ()
run opts
  | optShowHelp opts = putUsageInfo
  | null (optInputFiles opts) = do
    putStrLn "No input file.\n"
    putUsageInfo
  | otherwise = mapM_ (processInputFile opts) (optInputFiles opts)

-- | Processes the given input file.
--
--   The Haskell module is loaded and converted to Coq. The resulting Coq
--   AST is written to the console or output file.
processInputFile :: Options -> FilePath -> IO ()
processInputFile opts inputFile = do
  haskellAst <- parseModuleFile inputFile
  let coqAst = convertModuleWithPreamble haskellAst (optConversionMonad opts)
  case (optOutputDir opts) of
    Nothing -> putPretty coqAst
    Just outputDir ->
      let outputFileName = outputFileNameFor inputFile outputDir "v"
      in  writePrettyFile outputFileName coqAst

-- | Builds the file name of the output file for the given input file.
outputFileNameFor
  :: FilePath -- ^ The name of the input file.
  -> FilePath -- ^ The path to the output directory.
  -> String   -- ^ The extension of the output file.
  -> FilePath
outputFileNameFor inputFile outputDir extension =
  outputDir </> takeBaseName inputFile <.> extension

-------------------------------------------------------------------------------
-- REPL shortcuts                                                            --
-------------------------------------------------------------------------------

compileAndPrintFile :: String -> IO ()
compileAndPrintFile f = run defaultOptions { optInputFiles = [f] }

compileAndSaveFile :: String -> IO ()
compileAndSaveFile f = run defaultOptions
  { optInputFiles = [f]
  , optOutputDir  = Just "./CoqFiles/OutputFiles/"
  }

parseAndPrintFile :: String -> IO ()
parseAndPrintFile f = do
  ast <- parseModuleFile f
  print ast

testAst :: IO ()
testAst = parseAndPrintFile "TestModules/Test.hs"

test :: IO ()
test = compileAndPrintFile "TestModules/Test.hs"

saveTest :: IO ()
saveTest = compileAndSaveFile "TestModules/Test.hs"

savePrelude :: IO ()
savePrelude = compileAndSaveFile "TestModules/Prelude.hs"
