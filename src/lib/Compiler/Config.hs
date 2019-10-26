-- | This module contains utility functions for working with TOML
--   configuration files and JSON data.

module Compiler.Config
  ( loadConfig
  , saveConfig
  )
where

import qualified Data.Aeson                    as Aeson
import qualified Data.Aeson.Encode.Pretty      as AesonPretty
import qualified Data.ByteString.Lazy          as B
import qualified Data.Text                     as T
import           Data.String                    ( fromString )
import           System.FilePath
import qualified Text.Parsec.Error             as Parsec
import           Text.Toml                      ( parseTomlDoc )
import qualified Text.Toml.Types               as Toml

import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Reporter

-- | Loads a @.json@ or @.toml@ file and decodes its contents using
--   the "Aeson" interface.
--
--   The configuration file type is inferred from the file extension.
loadConfig :: Aeson.FromJSON a => FilePath -> ReporterIO a
loadConfig filename = reportIOErrors $ do
  contents <- lift $ readFile filename
  case takeExtension filename of
    ".toml" -> hoist $ decodeTomlConfig filename contents
    ".json" -> hoist $ decodeJsonConfig filename contents
    '.' : format ->
      reportFatal
        $  Message (FileSpan filename) Error
        $  "Unknown configuration file format: "
        ++ format
    _ ->
      reportFatal
        $ Message (FileSpan filename) Error
        $ "Missing extension. Cannot determine configuration file format."

-- | Parses a @.toml@ configuration file with the given contents.
decodeTomlConfig :: Aeson.FromJSON a => FilePath -> String -> Reporter a
decodeTomlConfig filename contents =
  case parseTomlDoc filename (T.pack contents) of
    Right document   -> decodeTomlDocument document
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
  decodeTomlDocument :: Aeson.FromJSON a => Toml.Table -> Reporter a
  decodeTomlDocument document = case Aeson.fromJSON (Aeson.toJSON document) of
    Aeson.Error msg -> do
      reportFatal
        $  Message (FileSpan filename) Error
        $  "Invalid configuration file format: "
        ++ msg
    Aeson.Success result -> return result

-- | Parses a @.json@ file with the given contents.
decodeJsonConfig :: Aeson.FromJSON a => FilePath -> String -> Reporter a
decodeJsonConfig filename contents =
  case Aeson.eitherDecode (fromString contents) of
    Right result   -> return result
    Left  errorMsg -> reportFatal $ Message (FileSpan filename) Error errorMsg

-- | Encodes the given value using its "Aeson" interface and saves
--   the encoded value as @.json@ file.
saveConfig :: Aeson.ToJSON a => FilePath -> a -> ReporterIO ()
saveConfig filename =
  reportIOErrors . lift . B.writeFile filename . AesonPretty.encodePretty
