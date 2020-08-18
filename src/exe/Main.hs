-- | This is the main module for the compiler's command line interface.
module Main where

import           Control.Monad ( (>=>) )
import           Control.Monad.Extra ( unlessM, whenM )
import           Control.Monad.IO.Class
import           Data.List ( intercalate )
import           Data.List.Extra ( splitOn )
import qualified Data.Map.Strict as Map
import           System.Directory ( createDirectoryIfMissing, doesFileExist )
import           System.Exit ( exitSuccess )
import           System.FilePath

import           FreeC.Application.Debug
import           FreeC.Application.Option.Help
import           FreeC.Application.Option.Version
import           FreeC.Application.Options
import           FreeC.Application.Options.Parser
import           FreeC.Backend
import           FreeC.Environment
import           FreeC.Environment.ModuleInterface.Decoder
import           FreeC.Environment.ModuleInterface.Encoder
import           FreeC.Frontend
import qualified FreeC.IR.Base.Prelude as IR.Prelude
import qualified FreeC.IR.Base.Test.QuickCheck as IR.Test.QuickCheck
import           FreeC.IR.DependencyGraph
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax as IR
import           FreeC.Monad.Application
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pipeline
import           FreeC.Pretty ( putPrettyLn, showPretty, writePrettyFile )

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
  getOpts >>= liftReporterIO . getAndParseArgs >>= putOpts
  -- Show help message if the user specified the @--help@ option.
  whenM (inOpts optShowHelp)
    $ liftIO
    $ do
      putUsageInfo
      exitSuccess
  -- Print version information if the user specified the @--version@ option.
  whenM (inOpts optShowVersion)
    $ liftIO
    $ do
      putVersionInfo
      exitSuccess
  -- Show usage information if there are no input files.
  whenM (inOpts (null . optInputFiles))
    $ liftIO
    $ do
      putDebug "No input file.\n"
      putUsageInfo
      exitSuccess
  -- Select frontend and backend
  frontend <- selectFrontend
  backend <- selectBackend
  -- Initialize environment.
  loadPrelude
  loadQuickCheck
  backendSpecialAction backend
  -- Process input files.
  modules <- inOpts optInputFiles
    >>= mapM (parseInputFile $ frontendParseFile frontend)
    >>= sortInputModules
  modules' <- mapM (convertInputModule $ backendConvertModule backend) modules
  mapM_ (uncurry (outputModule $ backendFileExtension backend)) modules'

-------------------------------------------------------------------------------
-- Front- and Backend Selection                                              --
-------------------------------------------------------------------------------
-- | Selects the correct frontend or throws an error if such a frontend does
--   not exist.
selectFrontend :: Application Frontend
selectFrontend = do
  name <- inOpts optFrontend
  case Map.lookup name frontends of
    Nothing -> do
      reportFatal
        $ Message NoSrcSpan Error
        $ "Unrecognized frontend. Currently supported frontends are: "
        ++ showFrontends
        ++ "."
    Just f  -> return f

-- | Selects the correct backend or throws an error if such a backend does
--   not exist.
selectBackend :: Application Backend
selectBackend = do
  name <- inOpts optBackend
  case Map.lookup name backends of
    Nothing -> do
      reportFatal
        $ Message NoSrcSpan Error
        $ "Unrecognized backend. Currently supported backends are: "
        ++ showBackends
        ++ "."
    Just b  -> return b

-------------------------------------------------------------------------------
-- Input Files                                                               --
-------------------------------------------------------------------------------
-- | Parses the given input file with the given parser function.
parseInputFile
  :: (SrcFile -> Application IR.Module) -> FilePath -> Application IR.Module
parseInputFile parser inputFile = reportApp
  $ do
    -- Parse and simplify input file.
    putDebug $ "Loading " ++ inputFile
    contents <- liftIO $ readFile inputFile
    parser $ mkSrcFile inputFile contents

-- | Sorts the given modules based on their dependencies.
--
--   If the module dependencies form a cycle, a fatal error is reported.
sortInputModules :: [IR.Module] -> Application [IR.Module]
sortInputModules = mapM checkForCycle . groupModules
 where
   checkForCycle :: DependencyComponent IR.Module -> Application IR.Module
   checkForCycle (NonRecursive m) = return m
   checkForCycle (Recursive ms)   = reportFatal
     $ Message NoSrcSpan Error
     $ "Module imports form a cycle: "
     ++ intercalate ", " (map (showPretty . IR.modName) ms)

-- | Converts the given module with the given converter function.
--
--   The resulting string is written to the console or output file.
convertInputModule :: (IR.Module -> Application String)
                   -> IR.Module
                   -> Application (IR.ModName, String)
convertInputModule converter ast = do
  let modName = IR.modName ast
      srcSpan = IR.modSrcSpan ast
  if hasSrcSpanFilename srcSpan
    then putDebug
      $ "Compiling "
      ++ showPretty modName
      ++ " ("
      ++ srcSpanFilename srcSpan
      ++ ")"
    else putDebug $ "Compiling " ++ showPretty modName
  reportApp
    $ do
      loadRequiredModules ast
      prog <- moduleEnv $ (liftConverter . runPipeline >=> converter) ast
      return (modName, prog)

-------------------------------------------------------------------------------
-- Output                                                                    --
-------------------------------------------------------------------------------
-- | Output a module that has been generated from a IR module
--   with the given name.
--
--  The generated file has the given file extension.
outputModule :: String -> IR.ModName -> String -> Application ()
outputModule ext modName outputStr = do
  maybeOutputDir <- inOpts optOutputDir
  case maybeOutputDir of
    Nothing        -> liftIO $ putPrettyLn outputStr
    Just outputDir -> do
      let outputPath = map (\c -> if c == '.' then '/' else c) modName
          outputFile = outputDir </> outputPath <.> ext
          ifaceFile  = outputDir </> outputPath <.> "json"
      Just iface <- inEnv $ lookupAvailableModule modName
      liftIO $ createDirectoryIfMissing True (takeDirectory outputFile)
      writeModuleInterface ifaceFile iface
      liftIO $ writePrettyFile outputFile outputStr

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------
-- | Loads the environments of modules imported by the given modules from
--   their environment file.
loadRequiredModules :: IR.Module -> Application ()
loadRequiredModules = mapM_ loadImport . IR.modImports

-- | Loads the environment of the module imported by the given declaration.
loadImport :: IR.ImportDecl -> Application ()
loadImport decl = do
  let srcSpan = IR.importSrcSpan decl
      modName = IR.importName decl
  unlessM (liftConverter (inEnv (isModuleAvailable modName)))
    $ loadModule srcSpan modName

-- | Loads the interface of the module with the given name from the
--   configured import path.
--
--   The given source span is used in error messages if the module could
--   not be found.
loadModule :: SrcSpan -> IR.ModName -> Application ()
loadModule srcSpan modName = do
  importDirs <- inOpts optImportDirs
  ifaceFile <- findIfaceFile importDirs
  iface <- loadModuleInterface ifaceFile
  modifyEnv $ makeModuleAvailable iface
 where
   -- | The name of the module's interface file relative to the import
   --   directories.
   filename :: FilePath
   filename = map (\c -> if c == '.' then '/' else c) modName <.> "json"

   -- | Looks for the module's interface file in the import directories.
   --
   --   Reports a fatal message if the file could not be found.
   findIfaceFile :: [FilePath] -> Application FilePath
   findIfaceFile []       = reportFatal
     $ Message srcSpan Error
     $ "Could not find imported module " ++ showPretty modName
   findIfaceFile (d : ds) = do
     let ifaceFile = d </> filename
     exists <- liftIO $ doesFileExist ifaceFile
     if exists then return ifaceFile else findIfaceFile ds

-------------------------------------------------------------------------------
-- Base Library                                                              --
-------------------------------------------------------------------------------
-- | Loads the @Prelude@ module from the base library.
loadPrelude :: Application ()
loadPrelude = loadModuleFromBaseLib IR.Prelude.modName

-- | Loads the @Test.QuickCheck@ module.
loadQuickCheck :: Application ()
loadQuickCheck = loadModuleFromBaseLib IR.Test.QuickCheck.modName

-- | Loads the module with the given name from the base library.
--
--   If the `--base-library` option is omitted, this function looks for the
--   base library in the `data-files` field of the `.cabal` file.
loadModuleFromBaseLib :: IR.ModName -> Application ()
loadModuleFromBaseLib modName = do
  baseLibDir <- inOpts optBaseLibDir
  let modPath   = joinPath $ splitOn "." modName
      ifaceFile = baseLibDir </> modPath <.> "toml"
  ifrace <- loadModuleInterface ifaceFile
  modifyEnv $ makeModuleAvailable ifrace
