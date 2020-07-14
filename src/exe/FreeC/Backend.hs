-- | This module contains the 'Backend' data type and all available backends.

module FreeC.Backend
  ( Backend(..)
  , backends
  , showBackends
  , defaultBackend
  )
where

import           Control.Monad.Extra            ( unlessM
                                                , whenM
                                                )
import           Control.Monad.IO.Class
import qualified Data.Map.Lazy                 as Map
import           Data.Maybe                     ( isJust )
import           Data.List                      ( intercalate )
import           System.Directory               ( createDirectoryIfMissing
                                                , doesFileExist
                                                , makeAbsolute
                                                )
import           System.FilePath

import           FreeC.Application.Options
import qualified FreeC.Backend.Agda.Converter.Module
                                               as Agda.Converter
import           FreeC.Backend.Agda.Pretty
import qualified FreeC.Backend.Coq.Base        as Coq.Base
import qualified FreeC.Backend.Coq.Converter.Module
                                               as Coq.Converter
import           FreeC.Backend.Coq.Pretty
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Application
import           FreeC.Pretty                   ( showPretty )

-- | Data type that represents a backend.
data Backend = Backend
  { backendName          :: String
    -- ^ The name of the backend.
  , backendConvertModule :: IR.Module -> Application String
    -- ^ The conversion function that converts a module to program text.
  , backendFileExtension :: String
    -- ^ The file extension associated with the backend.
  , backendSpecialAction :: Application ()
    -- ^ An action that has to performed by the backend before conversion, e.g.
    --   project file creation.
  }

-- | A map of all available backends with the name of those backends as keys.
backends :: Map.Map String Backend
backends = Map.fromList [ (backendName b, b) | b <- [coqBackend, irBackend, agdaBackend] ]

-- | Shows a list of all backends.
showBackends :: String
showBackends = '`' : intercalate "`, `" (Map.keys backends) ++ "`"

-- | Shows the name of the default backend.
defaultBackend :: String
defaultBackend = backendName coqBackend

-------------------------------------------------------------------------------
-- IR backend                                                                --
-------------------------------------------------------------------------------

-- | A dummy backend that just pretty prints the IR.
irBackend :: Backend
irBackend = Backend { backendName          = "ir"
                    , backendConvertModule = return . showPretty
                    , backendFileExtension = "ir"
                    , backendSpecialAction = return ()
                    }

-------------------------------------------------------------------------------
-- Coq backend                                                               --
-------------------------------------------------------------------------------

-- | Converts a module to a Coq program.
convertModuleToCoq :: IR.Module -> Application String
convertModuleToCoq ast = do
  ast' <- liftConverter $ Coq.Converter.convertModule ast
  return $ showPretty $ map PrettyCoq ast'

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

-- | The Coq backend.
coqBackend :: Backend
coqBackend = Backend { backendName          = "coq"
                     , backendConvertModule = convertModuleToCoq
                     , backendFileExtension = "v"
                     , backendSpecialAction = createCoqProject
                     }

-------------------------------------------------------------------------------
-- Agda backend                                                              --
-------------------------------------------------------------------------------

-- | Converts an IR module to a Coq program.
convertModuleToAgda :: IR.Module -> Application String
convertModuleToAgda ast = do
  ast' <- liftConverter $ Agda.Converter.convertModule ast
  return $ showPretty $ PrettyAgda ast'

-- | The Agda backend.
agdaBackend :: Backend
agdaBackend = Backend { backendName          = "agda"
                      , backendConvertModule = convertModuleToAgda
                      , backendFileExtension = "agda"
                      , backendSpecialAction = return ()
                      }
