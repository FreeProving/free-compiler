module Main where

import           Control.Monad.Extra            ( ifM
                                                , unlessM
                                                , whenM
                                                )
import           Control.Monad.IO.Class
import           Data.List                      ( intercalate )
import           Data.List.Extra                ( splitOn )
import           Data.Maybe                     ( isJust )
import qualified Language.Haskell.Exts.Syntax  as H
import           System.Directory               ( createDirectoryIfMissing
                                                , doesFileExist
                                                , makeAbsolute
                                                )
import           System.Exit                    ( exitSuccess )
import           System.FilePath

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Application.Debug
import           Compiler.Application.Options
import           Compiler.Converter             ( convertModule )
import           Compiler.Converter.QuickCheck
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Coq.Pretty
import           Compiler.Environment
import           Compiler.Environment.ModuleInterface.Decoder
import           Compiler.Environment.ModuleInterface.Encoder
import           Compiler.Frontend.Haskell.Parser
                                                ( parseModuleFile
                                                , parseModuleFileWithComments
                                                )
import           Compiler.Frontend.Haskell.PatternMatching
                                                ( transformPatternMatching )
import           Compiler.Frontend.Haskell.Pretty
                                                ( )
import           Compiler.Frontend.Haskell.Simplifier
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Application
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
  getOpts >>= liftReporterIO . getAndParseArgs >>= putOpts
  -- Show help message.
  whenM (inOpts optShowHelp) $ liftIO $ do
    putUsageInfo
    exitSuccess
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
parseInputFile :: FilePath -> Application HS.Module
parseInputFile inputFile = reportApp $ do
  -- Parse and simplify input file.
  (haskellAst, comments) <- liftReporterIO
    $ parseModuleFileWithComments inputFile
  haskellAst' <- transformInputModule haskellAst
  liftConverter (simplifyModuleWithComments haskellAst' comments)

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
      srcSpan = HS.modSrcSpan haskellAst
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
    coqAst <- liftConverter $ convertModule haskellAst
    return (modName, coqAst)

-------------------------------------------------------------------------------
-- Pattern matching compilation                                              --
-------------------------------------------------------------------------------

-- | Applies Haskell source code transformations if they are enabled.
transformInputModule :: H.Module SrcSpan -> Application (H.Module SrcSpan)
transformInputModule haskellAst = ifM (inOpts optTransformPatternMatching)
                                      transformPatternMatching'
                                      (return haskellAst)
 where
  transformPatternMatching' :: Application (H.Module SrcSpan)
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
        liftReporterIO $ parseModuleFile dumpFile

-------------------------------------------------------------------------------
-- Output                                                                    --
-------------------------------------------------------------------------------

-- | Output a Coq module that has been generated from a Haskell module
--   with the given name.
outputCoqModule :: HS.ModName -> [G.Sentence] -> Application ()
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
      liftReporterIO $ writeModuleInterface ifaceFile iface
      liftIO $ writePrettyFile outputFile (map PrettyCoq coqAst)

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------

-- | Loads the environments of modules imported by the given modules from
--   their environment file.
loadRequiredModules :: HS.Module -> Application ()
loadRequiredModules = mapM_ loadImport . HS.modImports

-- | Loads the environment of the module imported by the given declaration.
loadImport :: HS.ImportDecl -> Application ()
loadImport decl = do
  let srcSpan = HS.importSrcSpan decl
      modName = HS.importName decl
  unlessM (liftConverter (inEnv (isModuleAvailable modName)))
    $ loadModule srcSpan modName

-- | Loads the interface of the module with the given name from the
--   configured import path.
--
--   The given source span is used in error messages if the module could
--   not be found.
loadModule :: SrcSpan -> HS.ModName -> Application ()
loadModule srcSpan modName = do
  importDirs <- inOpts optImportDirs
  ifaceFile  <- findIfaceFile importDirs
  iface      <- liftReporterIO $ loadModuleInterface ifaceFile
  modifyEnv $ makeModuleAvailable iface
 where
  -- | The name of the module's interface file relative to the import
  --   directories.
  filename :: FilePath
  filename = (map (\c -> if c == '.' then '/' else c) modName) <.> "json"

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
loadPrelude = loadModuleFromBaseLib HS.preludeModuleName

-- | Loads the @Test.QuickCheck@ module.
loadQuickCheck :: Application ()
loadQuickCheck = loadModuleFromBaseLib quickCheckModuleName

-- | Loads the module with the given name from the base library.
--
--   If the `--base-library` option is omited, this function looks for the
--   base library in the `data-files` field of the `.cabal` file.
loadModuleFromBaseLib :: HS.ModName -> Application ()
loadModuleFromBaseLib modName = do
  baseLibDir <- inOpts optBaseLibDir
  let modPath   = joinPath $ splitOn "." modName
      ifaceFile = baseLibDir </> modPath <.> "toml"
  ifrace <- liftReporterIO $ loadModuleInterface ifaceFile
  modifyEnv $ makeModuleAvailable ifrace

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
      [ "-R " ++ relBaseDir ++ " " ++ showPretty CoqBase.baseLibName
      , "-R . " ++ showPretty CoqBase.generatedLibName
      ]
