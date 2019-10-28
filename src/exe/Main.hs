module Main where

import           Control.Monad                  ( join )
import           Control.Monad.Extra            ( unlessM )
import           Data.List
import           System.Console.GetOpt
import           System.Directory               ( createDirectoryIfMissing
                                                , doesFileExist
                                                , makeAbsolute
                                                )
import           System.Environment             ( getArgs
                                                , getProgName
                                                )
import           System.FilePath
import           System.IO                      ( stderr )

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Converter             ( convertModule )
import           Compiler.Coq.Pretty            ( )
import           Compiler.Environment
import           Compiler.Environment.Encoder
import           Compiler.Environment.Decoder
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Parser        ( parseModuleFile )
import           Compiler.Haskell.Simplifier
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty                ( putPrettyLn
                                                , showPretty
                                                , writePrettyFile
                                                )

import           Paths_haskellToCoqCompiler     ( getDataFileName )

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

  , optBaseLibDir :: FilePath
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
makeDefaultOptions :: IO Options
makeDefaultOptions = do
  defaultBaseLibDir <- getDataFileName "base"
  return $ Options
    { optShowHelp         = False
    , optInputFiles       = []
    , optOutputDir        = Nothing
    , optBaseLibDir       = defaultBaseLibDir
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
      (ReqArg (\p opts -> opts { optBaseLibDir = p }) "DIR")
      (  "Optional. Path to directory that contains the compiler's Coq\n"
      ++ "Base library. By default the compiler will look for the Base\n"
      ++ "library in it's data directory."
      )
    , Option
      []
      ["no-coq-project"]
      (NoArg (\opts -> opts { optCreateCoqProject = False }))
      (  "Disables the creation of a `_CoqProject` file in the output\n"
      ++ "directory. If the `--output` option is missing or the `_CoqProject`\n"
      ++ "file exists already, no `_CoqProject` is created.\n"
      )
    ]

-- | Parses the command line arguments.
--
--   If there are errors when parsing the command line arguments, a fatal
--   error message is reported.
--
--   All non-option arguments are considered as input files.
--
--   Returns the default options (see 'makeDefaultOptions') if no arguments are
--   specified.
parseArgs
  :: [String] -- ^ The command line arguments.
  -> ReporterIO Options
parseArgs args
  | null errors = do
    defaultOptions <- lift $ makeDefaultOptions
    let opts = foldr ($) defaultOptions optSetters
    return opts { optInputFiles = nonOpts }
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
  opts <- parseArgs args
  run opts

-- | Handles the given command line options.
--
--   Prints the help message if the @--help@ option or no input file was
--   specified. Otherwise all input files are processed (see
--   'processInputModule'). If a fatal message is reported while processing
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
    flip evalConverterT env $ do
      modules  <- mapM parseInputFile (optInputFiles opts)
      modules' <- lift' $ hoist $ sortInputModules modules
      actions  <- mapM (processInputModule opts) modules'
      return (sequence_ actions)

-------------------------------------------------------------------------------
-- Haskell input files                                                       --
-------------------------------------------------------------------------------

-- | Parses and simplifies the given input file.
--
--   If the module has no module header, its name is set to the base name
--   of the input file.
parseInputFile :: FilePath -> ConverterIO HS.Module
parseInputFile inputFile = do
  haskellAst <- lift' $ parseModuleFile inputFile
  hoist $ simplifyModule haskellAst

-- | Sorts the given modules based on their dependencies.
--
--   If the module dependencies form a cycle, a fatal error is reported.
sortInputModules :: [HS.Module] -> Reporter [HS.Module]
sortInputModules = mapM checkForCycle . groupModules
 where
  checkForCycle :: DependencyComponent HS.Module -> Reporter HS.Module
  checkForCycle (NonRecursive m) = return m
  checkForCycle (Recursive ms) =
    reportFatal
      $  Message NoSrcSpan Error
      $  "Module imports form a cycle: "
      ++ intercalate ", " (map (showPretty . HS.modName) ms)

-- | Converts the given Haskell module to Coq.
--
--   The resulting Coq AST is written to the console or output file.
processInputModule :: Options -> HS.Module -> ConverterIO (IO ())
processInputModule opts haskellAst = do
  coqAst <- hoist $ convertModule haskellAst
  case (optOutputDir opts) of
    Nothing        -> return (putPrettyLn coqAst)
    Just outputDir -> do
      let outputFileWithExt = outputFileFor haskellAst outputDir
          outputFile        = outputFileWithExt "v"
          envFile           = outputFileWithExt "json"
      lift $ createDirectoryIfMissing True (takeDirectory outputFile)
      getEnv >>= lift' . writeEnvironment envFile
      return (writePrettyFile outputFile coqAst)

-- | Builds the file name of the output file for the given module.
--
--   If the Haskell module has a module header, the output file name
--   is based on the module name. Otherwise, the output file name is
--   based on the input file name (as recorded in the source span).
outputFileFor
  :: HS.Module -- ^ The Haskell module AST.
  -> FilePath  -- ^ The path to the output directory.
  -> String    -- ^ The extension of the output file.
  -> FilePath
outputFileFor haskellAst outputDir extension =
  outputDir </> outputFile <.> extension
 where
  -- | The name of the output file relative to the output directory and
  --   without extension.
  outputFile :: FilePath
  outputFile = case HS.modName haskellAst >>= HS.identFromName of
    Nothing ->
      let inputFile = srcSpanFilename (HS.modSrcSpan haskellAst)
      in  intercalate "." (splitDirectories (dropExtension inputFile))
    Just modName -> map (\c -> if c == '.' then '/' else c) modName

-------------------------------------------------------------------------------
-- Base library                                                              --
-------------------------------------------------------------------------------

-- | Initializes the default environment using the specified path to the Coq
--   Base library.
--
--   If the `--base-library` option is omited, we look for the base library in
--   the `data-files` field of the `.cabal` file.
getDefaultEnvironment :: Options -> ReporterIO Environment
getDefaultEnvironment Options { optBaseLibDir = baseLibDir } =
  loadEnvironment (baseLibDir </> "env.toml")

-- | Creates a @_CoqProject@ file (if enabled) that maps the physical directory
--   of the Base library.
--
--   The path to the Base library will be relative to the output directory.
createCoqProject :: Options -> ReporterIO ()
createCoqProject Options { optOutputDir = Just outputDir, optBaseLibDir = baseDir, optCreateCoqProject = True }
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
  writeCoqProject = do
    createDirectoryIfMissing True outputDir
    contents <- makeContents
    writeFile coqProject contents

  -- | Creates the string to write to the 'coqProject' file.
  makeContents :: IO String
  makeContents = do
    absBaseDir   <- makeAbsolute baseDir
    absOutputDir <- makeAbsolute outputDir
    let relBaseDir = makeRelative absOutputDir absBaseDir
    return ("-R " ++ relBaseDir ++ " Base\n")
createCoqProject _ = return ()
