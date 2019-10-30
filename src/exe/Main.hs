module Main where

import           Control.Monad.Extra            ( unlessM
                                                , whenM
                                                )
import           Control.Monad.IO.Class
import           Data.List
import           Data.Maybe                     ( isJust )
import           System.Directory               ( createDirectoryIfMissing
                                                , doesFileExist
                                                , makeAbsolute
                                                )
import           System.Exit                    ( exitSuccess )
import           System.FilePath

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Monad.Application
import           Compiler.Application.Options
import           Compiler.Application.Debug
import           Compiler.Application.State
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

-------------------------------------------------------------------------------
-- Main                                                                      --
-------------------------------------------------------------------------------

-- | The main function of the compiler.
--
--   Runs the 'compiler' application and prints all reported messages
--   to @stderr@.
main :: IO ()
main = runApp compiler

-- | Parses and handles the command line options of the application.
--
--   Prints the help message if the @--help@ option or no input file was
--   specified. Otherwise all input files are processed (see
--   'processInputModule'). If a fatal message is reported while processing
--   any input file, the compiler will exit. All reported messages will be
--   printed to @stderr@.
compiler :: Application ()
compiler = do
  -- Parse command line arguments.
  defaultOpts <- inState appOpts
  opts        <- liftReporterIO $ getAndParseArgs defaultOpts
  modifyState $ setOpts opts
  -- Show help message.
  whenM (inState (optShowHelp . appOpts)) $ liftIO $ do
    putUsageInfo
    exitSuccess
  whenM (inState (null . optInputFiles . appOpts)) $ liftIO $ do
    putDebug "No input file.\n"
    putUsageInfo
    exitSuccess
  -- Process input files.
  env <- getDefaultEnvironment
  createCoqProject
  liftReporterIO $ flip evalConverterT env $ do
    modules  <- mapM parseInputFile (optInputFiles opts)
    modules' <- lift' $ hoist $ sortInputModules modules
    mapM_ (processInputModule opts) modules'

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
processInputModule :: Options -> HS.Module -> ConverterIO ()
processInputModule opts haskellAst = localEnv' $ do
  putDebug
    $  "Converting "
    ++ maybe "Main" showPretty (HS.modName haskellAst)
    ++ " ("
    ++ srcSpanFilename (HS.modSrcSpan haskellAst)
    ++ ")"
  coqAst <- hoist $ convertModule haskellAst
  case (optOutputDir opts) of
    Nothing        -> liftIO (putPrettyLn coqAst)
    Just outputDir -> do
      let outputFileWithExt = outputFileFor haskellAst outputDir
          outputFile        = outputFileWithExt "v"
          envFile           = outputFileWithExt "json"
      lift $ createDirectoryIfMissing True (takeDirectory outputFile)
      getEnv >>= lift' . writeEnvironment envFile
      liftIO (writePrettyFile outputFile coqAst)

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
getDefaultEnvironment :: Application Environment
getDefaultEnvironment = do
  baseLibDir <- inState $ optBaseLibDir . appOpts
  liftReporterIO $ loadEnvironment (baseLibDir </> "env.toml")

-- | Creates a @_CoqProject@ file (if enabled) that maps the physical directory
--   of the Base library.
--
--   The path to the Base library will be relative to the output directory.
createCoqProject :: Application ()
createCoqProject =
  whenM coqProjectEnabled $ unlessM coqProjectExists $ writeCoqProject
 where
  -- | Tests whether the generation of a @_CoqProject@ file is enabled.
  --
  --   The generation of the @_CoqProject@ file can be disabled with the
  --   command line option @--no-coq-project@. If there is no @--output@
  --   directory, the generation of the @_CoqProject@ file is disabled as
  --   well.
  coqProjectEnabled :: Application Bool
  coqProjectEnabled = do
    isEnabled      <- inState $ optCreateCoqProject . appOpts
    maybeOutputDir <- inState $ optOutputDir . appOpts
    return (isEnabled && isJust maybeOutputDir)

  -- | Path to the @_CoqProject@ file to create.
  getCoqProjectFile :: Application FilePath
  getCoqProjectFile = do
    Just outputDir <- inState $ optOutputDir . appOpts
    return (outputDir </> "_CoqProject")

  -- | Tests whether the @_CoqProject@ file does exist already.
  coqProjectExists :: Application Bool
  coqProjectExists = getCoqProjectFile >>= liftIO . doesFileExist

  -- | Writes the string returned by 'makeContents' to the @_CoqProject@ file.
  writeCoqProject :: Application ()
  writeCoqProject = do
    coqProject <- getCoqProjectFile
    contents   <- makeContents
    liftIO $ do
      createDirectoryIfMissing True (takeDirectory coqProject)
      writeFile coqProject contents

  -- | Creates the string to write to the 'coqProject' file.
  makeContents :: Application String
  makeContents = do
    baseDir        <- inState $ optBaseLibDir . appOpts
    Just outputDir <- inState $ optOutputDir . appOpts
    absBaseDir     <- liftIO $ makeAbsolute baseDir
    absOutputDir   <- liftIO $ makeAbsolute outputDir
    let relBaseDir = makeRelative absOutputDir absBaseDir
    return ("-R " ++ relBaseDir ++ " Base\n")
