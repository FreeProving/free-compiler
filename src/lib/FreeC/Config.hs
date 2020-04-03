-- | This module contains utility functions for working with TOML
--   configuration files and JSON data.

module FreeC.Config
  ( loadConfig
  , saveConfig
  )
where

import qualified Data.Aeson                    as Aeson
import qualified Data.Aeson.Encode.Pretty      as Aeson
import qualified Data.ByteString.Lazy          as LazyByteString
import           Data.String                    ( fromString )
import qualified Data.Text                     as Text
import           System.FilePath
import           Text.Toml                      ( parseTomlDoc )
import qualified Text.Toml.Types               as Toml

import           FreeC.IR.SrcSpan
import           FreeC.Monad.Reporter
import           FreeC.Util.Parsec

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
decodeTomlConfig filename contents = either
  (reportParsecError (mkSrcFileMap [mkSrcFile filename contents]))
  decodeTomlDocument
  (parseTomlDoc filename (Text.pack contents))
 where
  -- | Decodes a TOML document using the "Aeson" interace.
  decodeTomlDocument :: Aeson.FromJSON a => Toml.Table -> Reporter a
  decodeTomlDocument document = case Aeson.fromJSON (Aeson.toJSON document) of
    Aeson.Error msg ->
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
  reportIOErrors . lift . LazyByteString.writeFile filename . Aeson.encodePretty
