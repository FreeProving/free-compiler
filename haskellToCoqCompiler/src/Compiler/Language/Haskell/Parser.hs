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
import           Language.Haskell.Exts.SrcLoc   ( SrcSpanInfo )
import qualified Language.Haskell.Exts.Syntax  as H

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
--   The first parameter is the name of the source file and the second
--   parameter is the actual source code.
--
--   Exists the application if a syntax error is encountered.
parseModule :: String -> String -> IO (H.Module SrcSpanInfo)
parseModule filename contents =
  case parseModuleWithMode (parseMode filename) contents of
    ParseOk ast         -> return ast
    ParseFailed loc msg -> do
      -- TODO format error messages.
      putStrLn $ "Syntax Error in " ++ (prettyPrint loc) ++ ": " ++ msg
      -- TODO proper error handling that does not rely on IO
      exitFailure

-- | Loads and parses a Haskell module from the file with the given name.
--
--   Exists the application if a syntax error is encountered.
parseModuleFile :: String -> IO (H.Module SrcSpanInfo)
parseModuleFile filename = do
  contents <- readFile filename
  parseModule filename contents
