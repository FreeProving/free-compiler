module FreeC.Frontend
  ( Frontend(..)
  , haskellFrontend
  )
where

import           Control.Monad.Extra            ( ifM )
import           Control.Monad.IO.Class
import qualified Language.Haskell.Exts.Syntax  as HSE
import           System.Directory               ( createDirectoryIfMissing )
import           System.FilePath

import           FreeC.Application.Options
import           FreeC.Frontend.Haskell.Parser  ( parseHaskellModuleFile
                                                , parseHaskellModuleWithComments
                                                )
import           FreeC.Frontend.Haskell.PatternMatching
                                                ( transformPatternMatching )
import           FreeC.Frontend.Haskell.Pretty  ( )
import           FreeC.Frontend.Haskell.Simplifier
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Application
import           FreeC.Pretty                   ( writePrettyFile )

-- | Data type that represents a frontend.
data Frontend = Frontend
  { name      :: String
    -- ^ The name of the frontend.
  , parseFile :: SrcFile -> Application IR.Module
    -- ^ The parsing function that converts a file to the IR representation.
  }

  -------------------------------------------------------------------------------
  -- Haskell frontend                                                          --
  -------------------------------------------------------------------------------

-- | Parses and simplifies the given file.
parseHaskell :: SrcFile -> Application IR.Module
parseHaskell file = do
  (haskellAst, comments) <- parseHaskellModuleWithComments file
  haskellAst'            <- transformInputModule haskellAst
  liftConverter $ simplifyModuleWithComments haskellAst' comments

-- | The Haskell frontend.
haskellFrontend :: Frontend
haskellFrontend = Frontend { name = "haskell", parseFile = parseHaskell }

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
