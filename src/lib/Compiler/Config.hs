-- | This module contains utility functions for working with TOML configuration
--  files.

module Compiler.Config where

import qualified Data.Aeson                    as Aeson
import qualified Data.Text                     as T
import qualified Text.Parsec.Error             as Parsec
import           Text.Toml                      ( parseTomlDoc )
import qualified Text.Toml.Types               as Toml

import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Reporter

-- | Loads a `.toml` file from the given file and decodes it's contents
--   using the "Aeson" interface.
loadConfig :: Aeson.FromJSON a => FilePath -> ReporterIO a
loadConfig filename = reportIOErrors $ do
  contents <- lift $ readFile filename
  case parseTomlDoc filename (T.pack contents) of
    Right document   -> hoist $ decodeConfig document
    Left  parseError -> reportFatal $ Message
      (convertSrcSpan [(filename, lines contents)] (Parsec.errorPos parseError))
      Error
      ("Failed to parse config file: " ++ Parsec.showErrorMessages
        msgOr
        msgUnknown
        msgExpecting
        msgUnExpected
        msgEndOfInput
        (Parsec.errorMessages parseError)
      )
 where
  msgOr, msgUnknown, msgExpecting, msgUnExpected, msgEndOfInput :: String
  msgOr         = "or"
  msgUnknown    = "unknown parse error"
  msgExpecting  = "expecting"
  msgUnExpected = "unexpected"
  msgEndOfInput = "end of input"

  -- | Decodes a TOML document using the "Aeson" interace.
  decodeConfig :: Aeson.FromJSON a => Toml.Table -> Reporter a
  decodeConfig document = case Aeson.fromJSON (Aeson.toJSON document) of
    Aeson.Error msg -> do
      reportFatal
        $  Message (FileSpan filename) Error
        $  "Invalid configuration file format: "
        ++ msg
    Aeson.Success result -> return result
