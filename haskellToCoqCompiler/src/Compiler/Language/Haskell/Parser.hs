module Compiler.Language.Haskell.Parser
  ( parseModule
  , parseModuleFile
  )
where

import           System.Exit                    ( exitFailure )

import           Language.Haskell.Exts.Extension
                                                ( Language(..) )
import           Language.Haskell.Exts.Parser   ( ParseMode(..)
                                                , ParseResult(..)
                                                , parseModuleWithMode
                                                )
import           Language.Haskell.Exts.Pretty   ( prettyPrint )
import           Language.Haskell.Exts.SrcLoc   ( SrcLoc
                                                , SrcSpanInfo
                                                )
import qualified Language.Haskell.Exts.Syntax  as H

import           Compiler.Reporter

-- | Custom parameters for parsing a Haskell source file with the given name.
--
--   All language extensions are disabled and cannot be enabled using pragmas.
parseMode :: String -> ParseMode
parseMode filename = ParseMode
  { parseFilename         = filename
  , baseLanguage          = Haskell98
  , extensions            = []
  , ignoreLanguagePragmas = True
  , ignoreLinePragmas     = True
    -- TODO because we support some infix operations from the prelude
    -- we should specify their fixities here.
  , fixities              = Nothing
  , ignoreFunctionArity   = True
  }

-- | Parses a Haskell module.
--
--   Syntax errors cause a fatal error message to be reported.
parseModule
  :: String  -- ^ The name of the Haskell source file.
  -> String  -- ^ The Haskell source code.
  -> Reporter SrcLoc (H.Module SrcSpanInfo)
parseModule filename contents =
  case parseModuleWithMode (parseMode filename) contents of
    ParseOk ast         -> return ast
    ParseFailed loc msg -> reportFatal $ Message loc Error msg

-- | Loads and parses a Haskell module from the file with the given name.
--
--   Exists the application if a syntax error is encountered.
--   TODO Don't exit but return the reporter to the caller.
parseModuleFile
  :: String -- ^ The name of the Haskell source file.
  -> IO (H.Module SrcSpanInfo)
parseModuleFile filename = do
  contents <- readFile filename
  let reporter = parseModule filename contents
  printMessages (map (mapLocation prettyPrint) $ messages reporter)
  foldReporter reporter return exitFailure
