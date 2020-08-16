-- | This module contains the command line option parser.
module FreeC.Application.Options.Parser ( parseArgs, getAndParseArgs ) where

import           System.Console.GetOpt
import           System.Environment                    ( getArgs )

import           FreeC.Application.Options
import           FreeC.Application.Options.Descriptors
import           FreeC.IR.SrcSpan
import           FreeC.Monad.Reporter

-- | Parses the command line arguments.
--
--   If there are errors when parsing the command line arguments, a fatal
--   error message is reported.
--
--   All non-option arguments are considered input files.
--
--   Returns the default options (first argument) if no arguments are
--   specified.
parseArgs :: Options  -- ^ The default options.
  -> [ String ] -- ^ The command line arguments.
  -> Reporter Options
parseArgs defaultOptions args
  | null errors = do
    let opts = foldr ($) defaultOptions optSetters
    return opts { optInputFiles = nonOpts }
  | otherwise = do
    mapM_ (report . Message NoSrcSpan Error) errors
    reportFatal
      $ Message NoSrcSpan Error ("Failed to parse command line arguments.\n"
                                 ++ "Use '--help' for usage information.")
 where
   optSetters :: [ Options -> Options ]
   nonOpts :: [ String ]
   errors :: [ String ]
   (optSetters, nonOpts, errors) = getOpt Permute optionDescriptors args

-- | Gets the 'Options' for the command line arguments that were passed to
--   the application.
--
--   If there are no command line arguments the given default options are
--   returned. Otherwise the given options are modified accordingly.
getAndParseArgs :: Options -> ReporterIO Options
getAndParseArgs defaultOpts = do
  args <- lift getArgs
  hoist $ parseArgs defaultOpts args
