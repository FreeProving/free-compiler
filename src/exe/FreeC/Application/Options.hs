-- | This module contains the command line argument parser and the data type
--   that stores the values of the command line options.

module FreeC.Application.Options
  ( Options(..)
  , makeDefaultOptions
  )
where

import           Paths_free_compiler            ( getDataFileName )

import {-# SOURCE #-} FreeC.Backend
import {-# SOURCE #-} FreeC.Frontend

-- | Data type that stores the command line options passed to the compiler.
data Options = Options
  { optShowHelp                  :: Bool
    -- ^ Flag that indicates whether to show the usage information.

  , optShowVersion               :: Bool
    -- ^ Flag that indicates whether to show the compiler's version.

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
  , optFrontend                  :: String
    -- ^ The frontend to use.
  , optBackend                   :: String
    -- ^ The backend to use.
  }

-- | The default command line options.
--
--   The base library directory defaults to the @base/coq@ directory in the
--   cabal data directory.
--
--   By default output will be printed to the console.
--   The compiler looks for imported files in the current directory and
--   the output directory (if one is specified).
makeDefaultOptions :: IO Options
makeDefaultOptions = do
  defaultBaseLibDir <- getDataFileName "base"
  return $ Options { optShowHelp                  = False
                   , optShowVersion               = False
                   , optInputFiles                = []
                   , optOutputDir                 = Nothing
                   , optImportDirs                = ["."]
                   , optBaseLibDir                = defaultBaseLibDir
                   , optCreateCoqProject          = True
                   , optTransformPatternMatching  = False
                   , optDumpTransformedModulesDir = Nothing
                   , optFrontend                  = defaultFrontend
                   , optBackend                   = defaultBackend
                   }
