module Main where

import           Control.Monad                  ( join )
import           System.Environment             ( getArgs
                                                , getProgName
                                                )
import           System.Console.GetOpt
import           System.IO                      ( stderr )
import           System.FilePath

import           Compiler.Converter             ( convertModuleWithPreamble )
import           Compiler.Environment           ( Environment
                                                , emptyEnvironment
                                                )
import           Compiler.Environment.Loader
import           Compiler.Monad.Converter       ( evalConverter )
import           Compiler.Monad.Reporter
import           Compiler.Haskell.Parser        ( parseModuleFile )

import           Compiler.Haskell.Simplifier
import           Compiler.Pretty                ( putPrettyLn
                                                , writePrettyFile
                                                )
import           Compiler.Pretty.Coq            ( )
import           Compiler.Haskell.SrcSpan

-------------------------------------------------------------------------------
-- Command line option parser                                                --
-------------------------------------------------------------------------------

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

    -- | The directory that contains the Coq Base library that accompanies
    --   this compiler.
    optBaseLibDir :: Maybe FilePath
  }

-- | The default command line options.
--
--   By default output will be printed to the console.
defaultOptions :: Options
defaultOptions = Options
  { optShowHelp   = False
  , optInputFiles = []
  , optOutputDir  = Nothing
  , optBaseLibDir = Nothing
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
      ['b']
      ["base-library"]
      (ReqArg (\p opts -> opts { optBaseLibDir = Just p }) "DIR")
      (  "Optional. Path to directory that contains the compiler's Coq\n"
      ++ "Base library. If this argument is missing, you cannot use any\n"
      ++ "predefined types, constructors or functions (e.g. lists or\n"
      ++ "arithmetic expressions)."
      )
    ]

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
    mapM_ (report . Message NoSrcSpan Error) errors
    reportFatal $ Message
      NoSrcSpan
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

-------------------------------------------------------------------------------
-- Help message                                                              --
-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- Main                                                                      --
-------------------------------------------------------------------------------

-- | The main function of the compiler.
--
--   Parses the command line arguments and invokes 'run' if successful.
--   All reported messages are printed to @stderr@.
main :: IO ()
main = join $ reportToOrExit stderr $ reportIOErrors $ do
  args <- lift getArgs
  opts <- hoist $ parseArgs args
  run opts

-- | Handles the given command line options.
--
--   Prints the help message if the @--help@ option or no input file was
--   specified. Otherwise all input files are processed (see
--   'processInputFile'). If a fatal message is reported while processing
--   any input file, the compiler will exit. All reported messages will be
--   printed to @stderr@.
run :: Options -> ReporterIO (IO ())
run opts
  | optShowHelp opts = return putUsageInfo
  | null (optInputFiles opts) = do
    report $ Message NoSrcSpan Info "No input file."
    return putUsageInfo
  | otherwise = do
    env     <- getDefaultEnvironment opts
    actions <- mapM (processInputFile opts env) (optInputFiles opts)
    return (sequence_ actions)

-- | Initializes the default environment using the specified path to the Coq
--   Base library.
getDefaultEnvironment :: Options -> ReporterIO Environment
getDefaultEnvironment Options { optBaseLibDir = Nothing } = do
  report
    $  Message NoSrcSpan Warning
    $  "Missing path to Coq Base library. Predefined types, constructors and "
    ++ "functions will not be available!"
  report
    $  Message NoSrcSpan Info
    $  "Perhaps you want to add the '--base-library' command line argument to "
    ++ "make predefined types, constructors and functions available."
  return emptyEnvironment
getDefaultEnvironment Options { optBaseLibDir = Just baseLibDir } =
  loadEnvironment (baseLibDir </> "env.toml")

-- | Processes the given input file.
--
--   The Haskell module is loaded and converted to Coq. The resulting Coq
--   AST is written to the console or output file.
processInputFile :: Options -> Environment -> FilePath -> ReporterIO (IO ())
processInputFile opts env inputFile = do
  haskellAst <- parseModuleFile inputFile
  coqAst     <- hoist $ flip evalConverter env $ do
    haskellAst' <- simplifyModule haskellAst
    convertModuleWithPreamble haskellAst'

  return $ case (optOutputDir opts) of
    Nothing -> putPrettyLn coqAst
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
