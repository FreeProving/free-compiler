{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}

-- | This module contains the 'Frontend' data type and all available frontends.
module FreeC.Frontend
  ( Frontend(..)
  , FrontendParser
  , FrontendSimplifier
  , frontends
  , showFrontends
  , defaultFrontend
  ) where

import           Control.Monad.Extra                    ( ifM )
import           Control.Monad.IO.Class
import           Data.List                              ( intercalate )
import qualified Data.Map.Strict                        as Map
import qualified Language.Haskell.Exts.Syntax           as HSE
import           System.Directory
  ( createDirectoryIfMissing )
import           System.FilePath

import           FreeC.Application.Options
import           FreeC.Frontend.Haskell.Parser
  ( parseHaskellModuleWithComments )
import           FreeC.Frontend.Haskell.PatternMatching
  ( transformPatternMatching )
import           FreeC.Frontend.Haskell.Pretty          ()
import           FreeC.Frontend.Haskell.Simplifier
import           FreeC.Frontend.IR.Parser
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax                        as IR
import           FreeC.Monad.Application
import           FreeC.Pretty
  ( showPretty, writePrettyFile )

-- | Type synonym for a parsing function of a 'Frontend'.
type FrontendParser decls = SrcFile -> Application (IR.ModuleOf decls)

-- | Type synonym for a simplification function of a 'Frontend'.
type FrontendSimplifier decls = IR.ModuleOf decls -> Application IR.Module

-- | Data type that represents a frontend.
data Frontend = forall decls. Frontend
  { frontendName           :: String
    -- ^ The name of the frontend.
  , frontendParseFile      :: FrontendParser decls
    -- ^ The parsing function that parses the contents of an input file
    --   and converts the module header and import declarations to the
    --   intermediate representation. The remaining declarations of the
    --   module don't have to be converted in this phase.
  , frontendSimplifyModule :: FrontendSimplifier decls
    -- ^ The simplification function that converts a parsed module to the
    --   intermediate representation.
    --
    --   This function is applied after all input modules have been parsed
    --   and sorted topologically. Module interface files of modules that
    --   are imported by the input module are available in the environment.
  }

-- | A map of all available frontends with the name of those frontends as keys.
frontends :: Map.Map String Frontend
frontends
  = Map.fromList [(frontendName f, f) | f <- [haskellFrontend, irFrontend]]

-- | Shows a list of all frontends.
showFrontends :: String
showFrontends = '`' : intercalate "`, `" (Map.keys frontends) ++ "`"

-- | Shows the name of the default frontend.
defaultFrontend :: String
defaultFrontend = frontendName haskellFrontend

-------------------------------------------------------------------------------
-- IR Frontend                                                               --
-------------------------------------------------------------------------------
-- | A dummy frontend that just parses the IR.
irFrontend :: Frontend
irFrontend = Frontend { frontendName           = "ir"
                      , frontendParseFile      = parseIR @IR.Module
                      , frontendSimplifyModule = return
                      }

-------------------------------------------------------------------------------
-- Haskell Frontend                                                          --
-------------------------------------------------------------------------------
-- | Parses and simplifies the given file.
parseHaskell :: FrontendParser (HSE.Module SrcSpan)
parseHaskell inputFile = do
  (inputModule, comments) <- parseHaskellModuleWithComments inputFile
  liftConverter $ simplifyModuleHeadWithComments inputModule comments

-- | Simplifies the given Haskell module.
simplifyHaskell :: FrontendSimplifier (HSE.Module SrcSpan)
simplifyHaskell inputModule = do
  inputModule' <- transformInputModule inputModule
  liftConverter $ simplifyModuleBody inputModule'

-- | The Haskell frontend.
haskellFrontend :: Frontend
haskellFrontend = Frontend { frontendName           = "haskell"
                           , frontendParseFile      = parseHaskell
                           , frontendSimplifyModule = simplifyHaskell
                           }

-------------------------------------------------------------------------------
-- Pattern Matching Compilation                                              --
-------------------------------------------------------------------------------
-- | Applies Haskell source code transformations if they are enabled.
transformInputModule :: IR.ModuleOf (HSE.Module SrcSpan)
                     -> Application (IR.ModuleOf (HSE.Module SrcSpan))
transformInputModule inputModule = ifM (inOpts optTransformPatternMatching)
  transformPatternMatching' (return inputModule)
 where
  transformPatternMatching' :: Application (IR.ModuleOf (HSE.Module SrcSpan))
  transformPatternMatching' = do
    outputModule <- liftConverter
      $ transformPatternMatching (IR.modContents inputModule)
    maybeDumpDir <- inOpts optDumpTransformedModulesDir
    case maybeDumpDir of
      Nothing      -> return inputModule { IR.modContents = outputModule }
      Just dumpDir -> do
        -- Generate name of dump file.
        let modName = IR.modName inputModule
        let modPath      = map (\c -> if c == '.' then '/' else c) modName
            dumpFile     = dumpDir </> modPath <.> "hs"
            dumpContents = showPretty outputModule
        -- Dump the transformed module.
        liftIO $ createDirectoryIfMissing True (takeDirectory dumpFile)
        liftIO $ writePrettyFile dumpFile dumpContents
        -- Parse the dumped module, such that source spans in error messages
        -- refer to the dumped file. Since comments from the original module
        -- are discarded, the pragmas have to be added back.
        dumpModule <- parseHaskell (mkSrcFile dumpFile dumpContents)
        return dumpModule { IR.modPragmas = IR.modPragmas inputModule }
