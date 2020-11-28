-- | This is the main module for the compiler's command line interface.
module Main where

import           Control.Monad.Extra
  ( findM, unlessM, whenM )
import           Control.Monad.IO.Class
import           Data.List                                 ( intercalate )
import qualified Data.Map.Strict                           as Map
import           System.Directory
  ( createDirectoryIfMissing, doesFileExist )
import           System.Exit                               ( exitSuccess )
import           System.FilePath

import           FreeC.Application.Debug
import           FreeC.Application.Option.Help
import           FreeC.Application.Option.Version
import           FreeC.Application.Options
import           FreeC.Application.Options.Parser
import           FreeC.Backend
import           FreeC.Environment
import           FreeC.Environment.LookupOrFail
import           FreeC.Environment.ModuleInterface.Decoder
import           FreeC.Environment.ModuleInterface.Encoder
import           FreeC.Frontend
import qualified FreeC.IR.Base.Prelude                     as IR.Prelude
import           FreeC.IR.DependencyGraph
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax                           as IR
import           FreeC.Monad.Application
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pipeline
import           FreeC.Pretty
  ( putPrettyLn, showPretty, writePrettyFile )

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
--   'convertInputModuleWith'). If a fatal message is reported while processing
--   any input file, the compiler will exit. All reported messages will be
--   printed to @stderr@.
compiler :: Application ()
compiler = do
  -- Parse command line arguments.
  getOpts >>= liftReporterIO . getAndParseArgs >>= putOpts
  -- Show help message if the user specified the @--help@ option.
  whenM (inOpts optShowHelp) $ liftIO $ do
    putUsageInfo
    exitSuccess
  -- Print version information if the user specified the @--version@ option.
  whenM (inOpts optShowVersion) $ liftIO $ do
    putVersionInfo
    exitSuccess
  -- Show usage information if there are no input files.
  whenM (inOpts (null . optInputFiles)) $ liftIO $ do
    putDebug "No input file.\n"
    putUsageInfo
    exitSuccess
  -- Select frontend and backend
  frontend <- selectFrontend
  backend <- selectBackend
  -- Initialize environment.
  loadPrelude
  backendSpecialAction backend
  -- Process input files.
  case frontend of
    Frontend
      { frontendParseFile = parser, frontendSimplifyModule = simplifier } -> do
        let Backend { backendConvertModule = converter } = backend
        inputFiles <- inOpts optInputFiles
        inputModules <- mapM (parseInputFileWith parser) inputFiles
        sortedModules <- sortInputModules inputModules
        outputModules <- mapM (convertInputModuleWith simplifier converter)
          sortedModules
        mapM_ (uncurry (writeOutputModule backend)) outputModules

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
-- | Parses the given input file with the given parsing function.
parseInputFileWith
  :: FrontendParser decls -> FilePath -> Application (IR.ModuleOf decls)
parseInputFileWith parser inputFile = reportApp $ do
  putDebug $ "Loading " ++ inputFile
  contents <- liftIO $ readFile inputFile
  parser (mkSrcFile inputFile contents)

-- | Sorts the given modules based on their dependencies.
--
--   If the module dependencies form a cycle, a fatal error is reported.
sortInputModules :: [IR.ModuleOf decls] -> Application [IR.ModuleOf decls]
sortInputModules = mapM checkForCycle . groupModules
 where
  checkForCycle :: DependencyComponent (IR.ModuleOf decls)
                -> Application (IR.ModuleOf decls)
  checkForCycle (NonRecursive m) = return m
  checkForCycle (Recursive ms)   = reportFatal
    $ Message NoSrcSpan Error
    $ "Module imports form a cycle: "
    ++ intercalate ", " (map (showPretty . IR.modName) ms)

-- | Converts the given module with the given simplification and conversion
--   functions.
--
--   The resulting string is written to the console or output file.
convertInputModuleWith :: FrontendSimplifier decls
                       -> BackendConverter
                       -> IR.ModuleOf decls
                       -> Application (IR.ModName, String)
convertInputModuleWith simplifier converter inputModule = do
  let modName = IR.modName inputModule
      srcSpan = IR.modSrcSpan inputModule
  if hasSrcSpanFile srcSpan
    then putDebug
      $ "Compiling "
      ++ showPretty modName
      ++ " ("
      ++ srcFileName (srcSpanFile srcSpan)
      ++ ")"
    else putDebug $ "Compiling " ++ showPretty modName
  reportApp $ do
    loadRequiredModules inputModule
    moduleEnv $ do
      inputModule' <- simplifier inputModule
      outputModule <- liftConverter $ runPipeline inputModule'
      outputModule' <- converter outputModule
      return (modName, outputModule')

-------------------------------------------------------------------------------
-- Output                                                                    --
-------------------------------------------------------------------------------
-- | Output a module that has been generated by the given backend from an IR
--   module with the given name.
--
--   If the @--output@ command line option was specified, the output module is
--   written to a file whose name is based on the module name and whose
--   extension depends on the given back end. Otherwise, the output module is
--   printed to the console.
writeOutputModule :: Backend -> IR.ModName -> String -> Application ()
writeOutputModule backend modName outputStr = do
  maybeOutputDir <- inOpts optOutputDir
  case maybeOutputDir of
    Nothing        -> liftIO $ putPrettyLn outputStr
    Just outputDir -> do
      let outputPath = map (\c -> if c == '.' then '/' else c) modName
          outputFile
            = outputDir </> outputPath <.> backendFileExtension backend
          ifaceFile  = outputDir </> outputPath <.> "json"
      iface <- liftConverter $ lookupAvailableModuleOrFail NoSrcSpan modName
      liftIO $ createDirectoryIfMissing True (takeDirectory outputFile)
      writeModuleInterface ifaceFile iface
      liftIO $ writePrettyFile outputFile outputStr

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------
-- | Loads the environments of modules imported by the given modules from
--   their environment file.
loadRequiredModules :: IR.ModuleOf decls -> Application ()
loadRequiredModules = mapM_ loadImport . IR.modImports

-- | Loads the environment of the module imported by the given declaration.
loadImport :: IR.ImportDecl -> Application ()
loadImport decl = do
  let srcSpan = IR.importSrcSpan decl
      modName = IR.importName decl
  unlessM (liftConverter (inEnv (isModuleAvailable modName)))
    $ loadModule srcSpan modName

-- | Loads the interface of the module with the given name from the
--   configured import path or base library.
--
--   The given source span is used in error messages if the module could
--   not be found. Modules from the base library always take precedence.
--   Allowed file extensions for module interface files are @.json@ (for
--   generated module interfaces) and @.toml@ (for manually maintained
--   module interface files).
loadModule :: SrcSpan -> IR.ModName -> Application ()
loadModule srcSpan modName = do
  baseLibDir <- inOpts optBaseLibDir
  importDirs <- inOpts optImportDirs
  ifaceFile <- findIfaceFile (baseLibDir : importDirs)
  iface <- loadModuleInterface ifaceFile
  modifyEnv $ makeModuleAvailable iface
 where
  -- | The name of the module's interface file relative to the import
  --   directories.
  filename :: FilePath
  filename = map (\c -> if c == '.' then '/' else c) modName

  -- | The allowed file extensions of module interface files.
  extensions :: [String]
  extensions = ["json", "toml"]

  -- | Looks for the module's interface file in the import directories.
  --
  --   Reports a fatal message if the file could not be found.
  findIfaceFile :: [FilePath] -> Application FilePath
  findIfaceFile directories = do
    let ifaceFiles = [directory </> filename <.> extension
                     | directory <- directories
                     , extension <- extensions
                     ]
    ifraceFile <- findM (liftIO . doesFileExist) ifaceFiles
    maybe reportMissingModule return ifraceFile

  -- | Reports a fatal error message that the module could not be found.
  reportMissingModule :: Application a
  reportMissingModule = reportFatal
    $ Message srcSpan Error
    $ "Could not find imported module " ++ showPretty modName ++ "."

-------------------------------------------------------------------------------
-- Base Library                                                              --
-------------------------------------------------------------------------------
-- | Loads the @Prelude@ module from the base library.
--
--   This is the only module that we have to load explicitly, because the
--   import of @Prelude@ can be omitted.
loadPrelude :: Application ()
loadPrelude = loadModule NoSrcSpan IR.Prelude.modName
