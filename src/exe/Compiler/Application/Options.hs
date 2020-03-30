-- | This module contains the command line argument parser and the data type
--   that stores the values of the command line options.

module Compiler.Application.Options
  ( Options(..)
  , makeDefaultOptions
  , parseArgs
  , getAndParseArgs
  , putUsageInfo
  )
where

import           System.Console.GetOpt
import           System.Environment             ( getArgs
                                                , getProgName
                                                )

import           Compiler.IR.SrcSpan
import           Compiler.Monad.Reporter

import           Paths_free_compiler            ( getDataFileName )

-------------------------------------------------------------------------------
-- Command line option data type                                             --
-------------------------------------------------------------------------------

-- | Data type that stores the command line options passed to the compiler.
data Options = Options
  { optShowHelp                  :: Bool
    -- ^ Flag that indicates whether to show the usage information.

  , optInputFiles                :: [FilePath]
    -- ^ The input files passed to the compiler.
    --   All non-option command line arguments are considered input files.

  , optOutputDir                 :: Maybe FilePath
    -- ^ The output directory or 'Nothing' if the output should be printed
    --   to @stdout@.

  , optImportDirs                :: [FilePath]
    -- ^ The directories to look in for imported modules.

  , optBaseLibDir                :: FilePath
    -- ^ The directory that contains the Coq Base library that accompanies
    --   this compiler.

  , optCreateCoqProject          :: Bool
    -- ^ Flag that indicates whether to generate a @_CoqProject@ file in the
    --   ouput directory. This argument is ignored if 'optOutputDir' is not
    --   specified.

  , optTransformPatternMatching  :: Bool
    -- ^ Flag that indicates whether to transform pattern matching, perform
    --   guard elimination and case completion.

  , optDumpTransformedModulesDir :: Maybe FilePath
    -- ^ The directory to dump transformed modules to.
  }

-- | The default command line options.
--
--   The base library directory defaults to the @base@ directory in the
--   cabal data directory.
--
--   By default output will be printed to the console.
--   The compiler looks for imported files in the current directory and
--   the output directory (if one is specified).
makeDefaultOptions :: IO Options
makeDefaultOptions = do
  defaultBaseLibDir <- getDataFileName "base"
  return $ Options { optShowHelp                  = False
                   , optInputFiles                = []
                   , optOutputDir                 = Nothing
                   , optImportDirs                = ["."]
                   , optBaseLibDir                = defaultBaseLibDir
                   , optCreateCoqProject          = True
                   , optTransformPatternMatching  = False
                   , optDumpTransformedModulesDir = Nothing
                   }

-------------------------------------------------------------------------------
-- Command line option parser                                                --
-------------------------------------------------------------------------------

-- | Command line option descriptors from the @GetOpt@ library.
options :: [OptDescr (Options -> Options)]
options =
  [ Option ['h']
           ["help"]
           (NoArg (\opts -> opts { optShowHelp = True }))
           "Display this message."
  , Option
    ['o']
    ["output"]
    (ReqArg
      (\p opts ->
        opts { optOutputDir = Just p, optImportDirs = p : optImportDirs opts }
      )
      "DIR"
    )
    (  "Optional. Path to output directory.\n"
    ++ "Prints to the console by default."
    )
  , Option
    ['i']
    ["import"]
    (ReqArg (\p opts -> opts { optImportDirs = p : optImportDirs opts }) "DIR")
    (  "Optional. Adds the specified directory to the search path for\n"
    ++ "imported modules. The compiler looks in the current and output\n"
    ++ "directory by default. Multiple import directories can be added\n"
    ++ "by specifying additional `--import` options."
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
  , Option
    []
    ["transform-pattern-matching"]
    (NoArg (\opts -> opts { optTransformPatternMatching = True }))
    (  "Experimental. Enables the automatic transformation of pattern\n"
    ++ "matching, including guard elimination and case completion.\n"
    ++ "If this option is enabled, no location information will be\n"
    ++ "available in error messages."
    )
  , Option
    []
    ["dump-transformed-modules"]
    (ReqArg (\p opts -> opts { optDumpTransformedModulesDir = Just p }) "DIR")
    (  "If `--transform-pattern-matching` is enabled, the transformed\n"
    ++ "Haskell modules will be placed in the given directory.\n"
    ++ "This option adds location information to error messages that\n"
    ++ "refer to the dumped file."
    )
  ]

-- | Parses the command line arguments.
--
--   If there are errors when parsing the command line arguments, a fatal
--   error message is reported.
--
--   All non-option arguments are considered as input files.
--
--   Returns the default options (first argument) if no arguments are
--   specified.
parseArgs
  :: Options  -- ^ The default options.
  -> [String] -- ^ The command line arguments.
  -> Reporter Options
parseArgs defaultOptions args
  | null errors = do
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

-- | Gets the 'Options' for the command line arguments that were passed to
--   the application.
--
--   If there are no command line arguments the given default options are
--   returned. Otherwise the given options are modified accordingly.
getAndParseArgs :: Options -> ReporterIO Options
getAndParseArgs defaultOpts = do
  args <- lift getArgs
  hoist $ parseArgs defaultOpts args

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
