-- | This is the main module for the compiler's command line interface.

module Main where

import           Control.Monad.Extra            ( ifM
                                                , unlessM
                                                , whenM
                                                )
import           Control.Monad.IO.Class
import           Data.List                      ( intercalate )
import           Data.List.Extra                ( splitOn )
import           Data.Maybe                     ( isJust )
import qualified Language.Haskell.Exts.Syntax  as HSE
import           System.Directory               ( createDirectoryIfMissing
                                                , doesFileExist
                                                , makeAbsolute
                                                )
import           System.Exit                    ( exitSuccess )
import           System.FilePath

import           FreeC.Application.Debug
import           FreeC.Application.Option.Help
import           FreeC.Application.Option.Version
import           FreeC.Application.Options
import           FreeC.Application.Options.Parser
import qualified FreeC.Backend.Agda.Converter  as Agda
                                                ( convertModule )
import           FreeC.Backend.Agda.Pretty      ( )
import qualified FreeC.Backend.Coq.Base        as Coq.Base
import           FreeC.Backend.Coq.Converter    ( convertModule )
import           FreeC.Backend.Coq.Pretty
import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment
import           FreeC.Environment.ModuleInterface.Decoder
import           FreeC.Environment.ModuleInterface.Encoder
import           FreeC.Frontend.Haskell.Parser  ( parseHaskellModuleFile
                                                , parseHaskellModuleFileWithComments
                                                )
import           FreeC.Frontend.Haskell.PatternMatching
                                                ( transformPatternMatching )
import           FreeC.Frontend.Haskell.Pretty  ( )
import           FreeC.Frontend.Haskell.Simplifier
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Base.Prelude         as IR.Prelude
import qualified FreeC.IR.Base.Test.QuickCheck as IR.Test.QuickCheck
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Application
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty                   ( putPrettyLn
                                                , showPretty
                                                , writePrettyFile
                                                )

import           Debug.Trace

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
  -- Initialize environment.
  loadPrelude
  loadQuickCheck
  createCoqProject
  -- Process input files.
  modules  <- inOpts optInputFiles >>= mapM parseInputFile >>= sortInputModules
  modules' <- mapM convertInputModule modules
  mapM_ (uncurry outputCoqModule) modules'

-------------------------------------------------------------------------------
-- Haskell input files                                                       --
-------------------------------------------------------------------------------

-- | Parses and simplifies the given input file.
parseInputFile :: FilePath -> Application IR.Module
parseInputFile inputFile = reportApp $ do
  -- Parse and simplify input file.
  putDebug $ "Loading " ++ inputFile
  (haskellAst, comments) <- liftReporterIO
    $ parseHaskellModuleFileWithComments inputFile
  haskellAst' <- transformInputModule haskellAst
  liftConverter (simplifyModuleWithComments haskellAst' comments)

-- | Sorts the given modules based on their dependencies.
--
--   If the module dependencies form a cycle, a fatal error is reported.
sortInputModules :: [IR.Module] -> Application [IR.Module]
sortInputModules = mapM checkForCycle . groupModules
 where
  checkForCycle :: DependencyComponent IR.Module -> Application IR.Module
  checkForCycle (NonRecursive m) = return m
  checkForCycle (Recursive ms) =
    reportFatal
      $  Message NoSrcSpan Error
      $  "Module imports form a cycle: "
      ++ intercalate ", " (map (showPretty . IR.modName) ms)

-- | Converts the given Haskell module to Coq.
--
--   The resulting Coq AST is written to the console or output file.
convertInputModule :: IR.Module -> Application (IR.ModName, [Coq.Sentence])
convertInputModule haskellAst = do
  let modName = IR.modName haskellAst
      srcSpan = IR.modSrcSpan haskellAst
  if hasSrcSpanFilename srcSpan
    then
      putDebug
      $  "Compiling "
      ++ showPretty modName
      ++ " ("
      ++ srcSpanFilename srcSpan
      ++ ")"
    else putDebug $ "Compiling " ++ showPretty modName
  reportApp $ do
    loadRequiredModules haskellAst
    coqAst  <- liftConverter $ convertModule haskellAst
    agdaAst <- liftConverter $ Agda.convertModule haskellAst
    traceM $ showPretty agdaAst
    traceM $ undefined
    return (modName, coqAst)

-------------------------------------------------------------------------------
-- Pattern matching compilation                                              --
-------------------------------------------------------------------------------

-- | Applies Haskell source code transformations if they are enabled.
transformInputModule :: HSE.Module SrcSpan -> Application (HSE.Module SrcSpan)
transformInputModule haskellAst = ifM (inOpts optTransformPatternMatching)
                                      transformPatternMatching'
                                      (return haskellAst)
 where
  transformPatternMatching' :: Application (HSE.Module SrcSpan)
  transformPatternMatching' = do
    haskellAst'  <- liftConverter (transformPatternMatching haskellAst)
    maybeDumpDir <- inOpts optDumpTransformedModulesDir
    case maybeDumpDir of
      Nothing      -> return haskellAst'
      Just dumpDir -> do
        -- Generate name of dump file.
        modName <- liftConverter $ extractModName haskellAst'
        let modPath  = map (\c -> if c == '.' then '/' else c) modName
            dumpFile = dumpDir </> modPath <.> "hs"
        -- Dump the transformed module.
        liftIO $ createDirectoryIfMissing True (takeDirectory dumpFile)
        liftIO $ writePrettyFile dumpFile haskellAst'
        -- Read the dumped module back in, such that source spans in
        -- error messages refer to the dumped file.
        liftReporterIO $ parseHaskellModuleFile dumpFile

-------------------------------------------------------------------------------
-- Output                                                                    --
-------------------------------------------------------------------------------

-- | Output a Coq module that has been generated from a Haskell module
--   with the given name.
outputCoqModule :: IR.ModName -> [Coq.Sentence] -> Application ()
outputCoqModule modName coqAst = do
  maybeOutputDir <- inOpts optOutputDir
  case maybeOutputDir of
    Nothing        -> liftIO (putPrettyLn (map PrettyCoq coqAst))
    Just outputDir -> do
      let outputPath = map (\c -> if c == '.' then '/' else c) modName
          outputFile = outputDir </> outputPath <.> "v"
          ifaceFile  = outputDir </> outputPath <.> "json"
      Just iface <- inEnv $ lookupAvailableModule modName
      liftIO $ createDirectoryIfMissing True (takeDirectory outputFile)
      writeModuleInterface ifaceFile iface
      liftIO $ writePrettyFile outputFile (map PrettyCoq coqAst)

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
  ifaceFile  <- findIfaceFile importDirs
  iface      <- loadModuleInterface ifaceFile
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
  findIfaceFile [] =
    reportFatal
      $  Message srcSpan Error
      $  "Could not find imported module "
      ++ showPretty modName
  findIfaceFile (d : ds) = do
    let ifaceFile = d </> filename
    exists <- liftIO $ doesFileExist ifaceFile
    if exists then return ifaceFile else findIfaceFile ds

-------------------------------------------------------------------------------
-- Base library                                                              --
-------------------------------------------------------------------------------

-- | Loads the @Prelude@ module from the base library.
loadPrelude :: Application ()
loadPrelude = loadModuleFromBaseLib IR.Prelude.modName

-- | Loads the @Test.QuickCheck@ module.
loadQuickCheck :: Application ()
loadQuickCheck = loadModuleFromBaseLib IR.Test.QuickCheck.modName

-- | Loads the module with the given name from the base library.
--
--   If the `--base-library` option is omited, this function looks for the
--   base library in the `data-files` field of the `.cabal` file.
loadModuleFromBaseLib :: IR.ModName -> Application ()
loadModuleFromBaseLib modName = do
  baseLibDir <- inOpts optBaseLibDir
  let modPath   = joinPath $ splitOn "." modName
      ifaceFile = baseLibDir </> modPath <.> "toml"
  ifrace <- loadModuleInterface ifaceFile
  modifyEnv $ makeModuleAvailable ifrace

-- | Creates a @_CoqProject@ file (if enabled) that maps the physical directory
--   of the Base library.
--
--   The path to the Base library will be relative to the output directory.
createCoqProject :: Application ()
createCoqProject = whenM coqProjectEnabled
  $ unlessM coqProjectExists writeCoqProject
 where
  -- | Tests whether the generation of a @_CoqProject@ file is enabled.
  --
  --   The generation of the @_CoqProject@ file can be disabled with the
  --   command line option @--no-coq-project@. If there is no @--output@
  --   directory, the generation of the @_CoqProject@ file is disabled as
  --   well.
  coqProjectEnabled :: Application Bool
  coqProjectEnabled = do
    isEnabled      <- inOpts optCreateCoqProject
    maybeOutputDir <- inOpts optOutputDir
    return (isEnabled && isJust maybeOutputDir)

  -- | Path to the @_CoqProject@ file to create.
  getCoqProjectFile :: Application FilePath
  getCoqProjectFile = do
    Just outputDir <- inOpts optOutputDir
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
    baseDir        <- inOpts optBaseLibDir
    Just outputDir <- inOpts optOutputDir
    absBaseDir     <- liftIO $ makeAbsolute baseDir
    absOutputDir   <- liftIO $ makeAbsolute outputDir
    let relBaseDir = makeRelative absOutputDir absBaseDir
    return $ unlines
      [ "-R " ++ relBaseDir ++ " " ++ showPretty Coq.Base.baseLibName
      , "-R . " ++ showPretty Coq.Base.generatedLibName
      ]
