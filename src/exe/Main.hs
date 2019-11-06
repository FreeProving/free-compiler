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
import qualified Compiler.Coq.AST              as G
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
--   'convertInputModule'). If a fatal message is reported while processing
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
  -- Initialize environment.
  loadPrelude
  createCoqProject
  -- Process input files.
  modules  <- mapM parseInputFile (optInputFiles opts) >>= sortInputModules
  modules' <- mapM convertInputModule modules
  mapM_ (uncurry outputCoqModule) modules'

-------------------------------------------------------------------------------
-- Haskell input files                                                       --
-------------------------------------------------------------------------------

-- | Parses and simplifies the given input file.
parseInputFile :: FilePath -> Application HS.Module
parseInputFile inputFile = do
  -- Parse and simplify input file.
  haskellAst <- liftReporterIO $ parseModuleFile inputFile
  liftConverter (simplifyModule haskellAst)

-- | Sorts the given modules based on their dependencies.
--
--   If the module dependencies form a cycle, a fatal error is reported.
sortInputModules :: [HS.Module] -> Application [HS.Module]
sortInputModules = mapM checkForCycle . groupModules
 where
  checkForCycle :: DependencyComponent HS.Module -> Application HS.Module
  checkForCycle (NonRecursive m) = return m
  checkForCycle (Recursive ms) =
    reportFatal
      $  Message NoSrcSpan Error
      $  "Module imports form a cycle: "
      ++ intercalate ", " (map (showPretty . HS.modName) ms)

-- | Converts the given Haskell module to Coq.
--
--   The resulting Coq AST is written to the console or output file.
convertInputModule :: HS.Module -> Application (HS.ModName, [G.Sentence])
convertInputModule haskellAst = do
  let modName = HS.modName haskellAst
  putDebug
    $  "Compiling "
    ++ showPretty modName
    ++ " ("
    ++ srcSpanFilename (HS.modSrcSpan haskellAst)
    ++ ")"
  coqAst <- liftConverter $ convertModule haskellAst
  return (modName, coqAst)

-------------------------------------------------------------------------------
-- Output                                                                    --
-------------------------------------------------------------------------------

-- | Output a Coq module that has been generated from a Haskell module
--   with the given name.
outputCoqModule :: HS.ModName -> [G.Sentence] -> Application ()
outputCoqModule modName coqAst = do
  maybeOutputDir <- inState $ optOutputDir . appOpts
  case maybeOutputDir of
    Nothing        -> liftIO (putPrettyLn coqAst)
    Just outputDir -> do
      let outputPath = map (\c -> if c == '.' then '/' else c) modName
          outputFile = outputDir </> outputPath <.> "v"
          envFile    = outputDir </> outputPath <.> "json"
      Just env <- liftConverter $ inEnv $ lookupAvailableModule modName
      liftIO $ createDirectoryIfMissing True (takeDirectory outputFile)
      liftReporterIO $ writeEnvironment envFile env
      liftIO $ writePrettyFile outputFile coqAst

-------------------------------------------------------------------------------
-- Base library                                                              --
-------------------------------------------------------------------------------

-- | Loads the @Prelude@ module from the base library.
--
--   If the `--base-library` option is omited, this function looks for the
--   base library in the `data-files` field of the `.cabal` file.
loadPrelude :: Application ()
loadPrelude = do
  baseLibDir <- inState $ optBaseLibDir . appOpts
  preludeEnv <- liftReporterIO $ loadEnvironment (baseLibDir </> "Prelude.toml")
  liftConverter $ modifyEnv $ makeModuleAvailable HS.preludeModuleName
                                                  preludeEnv

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
