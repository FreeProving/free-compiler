module Main where

import           Control.Monad                  ( join )
import           Control.Monad.Extra            ( unlessM )
import           System.Console.GetOpt
import           System.Directory               ( doesFileExist
                                                , makeAbsolute
                                                )
import           System.Environment             ( getArgs
                                                , getProgName
                                                )
import           System.FilePath
import           System.IO                      ( stderr )

import           Compiler.Converter             ( convertModuleWithPreamble )
import           Compiler.Coq.Pretty            ( )
import           Compiler.Environment           ( Environment
                                                , defineProofs
                                                , emptyEnvironment
                                                )
import           Compiler.Environment.Loader
import           Compiler.Environment.ProofLoader
import           Compiler.Haskell.Parser        ( parseModuleFile )
import           Compiler.Haskell.Simplifier
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter       ( evalConverter
                                                , modifyEnv
                                                )
import           Compiler.Monad.Reporter
import           Compiler.Pretty                ( putPrettyLn
                                                , writePrettyFile
                                                )

-------------------------------------------------------------------------------
-- Command line option parser                                                --
-------------------------------------------------------------------------------

-- | Data type that stores the command line options passed to the compiler.
data Options = Options
  { optShowHelp   :: Bool
    -- ^ Flag that indicates whether to show the usage information.

  , optInputFiles :: [FilePath]
    -- ^ The input files passed to the compiler.
    --   All non-option command line arguments are considered input files.

  , optOutputDir  :: Maybe FilePath
    -- ^ The output directory or 'Nothing' if the output should be printed
    --   to @stdout@.

  , optBaseLibDir :: Maybe FilePath
    -- ^ The directory that contains the Coq Base library that accompanies
    --   this compiler.

  , optCreateCoqProject :: Bool
    -- ^ Flag that indicates whether to generate a @_CoqProject@ file in the
    --   ouput directory. This argument is ignored if 'optOutputDir' is not
    --   specified.
  }

-- | The default command line options.
--
--   By default output will be printed to the console.
defaultOptions :: Options
defaultOptions = Options
  { optShowHelp         = False
  , optInputFiles       = []
  , optOutputDir        = Nothing
  , optBaseLibDir       = Nothing
  , optCreateCoqProject = True
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
    , Option
      []
      ["no-coq-project"]
      (NoArg (\opts -> opts { optCreateCoqProject = False }))
      (  "Disables the creation of a `_CoqProject` file in the output\n"
      ++ "directory. If the `--output` or `--base-library` option is missing\n"
      ++ "or the `_CoqProject` file exists already, no `_CoqProject` is\n"
      ++ "created."
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
    env <- getDefaultEnvironment opts
    createCoqProject opts
    actions <- mapM (processInputFile opts env) (optInputFiles opts)
    return (sequence_ actions)

-------------------------------------------------------------------------------
-- Haskell input files                                                       --
-------------------------------------------------------------------------------

-- | Processes the given input file.
--
--   The Haskell module is loaded and converted to Coq. The resulting Coq
--   AST is written to the console or output file.
processInputFile :: Options -> Environment -> FilePath -> ReporterIO (IO ())
processInputFile opts env inputFile = do
  haskellAst <- parseModuleFile inputFile
  proofs     <- locateAndLoadProofsFor inputFile
  coqAst     <- hoist $ flip evalConverter env $ do
    modifyEnv $ defineProofs proofs
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

-------------------------------------------------------------------------------
-- Proofs for QuickCheck properties                                          --
-------------------------------------------------------------------------------

-- | Builds the file name of the `.toml` file that contains proofs for
--   QuickCheck properties.
proofFileNameFor :: FilePath -> FilePath
proofFileNameFor inputFile = dropExtension inputFile <.> "proofs" <.> "toml"

-- | Locates the `.poofs.toml` file (see 'proofFileNameFor') for the Haskell
--   module with the given file name and returns the proofs defined in it.
--
--   Returns an empty map if the proof file could not be found.
locateAndLoadProofsFor :: FilePath -> ReporterIO ProofMap
locateAndLoadProofsFor inputFile = do
  let proofFile = proofFileNameFor inputFile
  fileExists <- lift $ doesFileExist proofFile
  if fileExists then loadProofs proofFile else return emptyProofMap

-------------------------------------------------------------------------------
-- Base library                                                              --
-------------------------------------------------------------------------------

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

-- | Creates a @_CoqProject@ file (if enabled) that maps the physical directory
--   of the Base library.
--
--   The path to the Base library will be relative to the output directory.
createCoqProject :: Options -> ReporterIO ()
createCoqProject Options { optOutputDir = Just outputDir, optBaseLibDir = Just baseDir, optCreateCoqProject = True }
  = lift $ unlessM coqProjectExists $ writeCoqProject
 where
  -- | Path to the @_CoqProject@ file to create.
  coqProject :: FilePath
  coqProject = outputDir </> "_CoqProject"

  -- | Tests whether the 'coqProject' file does exist already.
  coqProjectExists :: IO Bool
  coqProjectExists = doesFileExist coqProject

  -- | Writes  'contents' to the 'coqProject' file.
  writeCoqProject :: IO ()
  writeCoqProject = makeContents >>= writeFile coqProject

  -- | Creates the string to write to the 'coqProject' file.
  makeContents :: IO String
  makeContents = do
    absBaseDir   <- makeAbsolute baseDir
    absOutputDir <- makeAbsolute outputDir
    let relBaseDir = makeRelative absOutputDir absBaseDir
    return ("-R " ++ relBaseDir ++ " Base\n")
createCoqProject _ = return ()
