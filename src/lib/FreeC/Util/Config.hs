-- | This module contains utility functions for working with TOML
--   configuration files and JSON data.
module FreeC.Util.Config ( loadConfig, saveConfig ) where

import           Control.Monad.IO.Class   ( MonadIO(..) )
import qualified Data.Aeson               as Aeson
import qualified Data.Aeson.Encode.Pretty as Aeson
import qualified Data.ByteString.Lazy     as LazyByteString
import           Data.String              ( fromString )
import           System.FilePath
import           Text.Toml                ( parseTomlDoc )
import qualified Text.Toml.Types          as Toml

import           FreeC.IR.SrcSpan
import           FreeC.Monad.Reporter
import           FreeC.Util.Parsec

-- | Loads a @.json@ or @.toml@ file and decodes its contents using
--   the "Aeson" interface.
--
--   The configuration file type is inferred from the file extension.
loadConfig :: (MonadIO r, MonadReporter r, Aeson.FromJSON a) => FilePath -> r a
loadConfig filename = do
  contents <- liftIO $ readFile filename
  let srcFile = mkSrcFile filename contents
  case takeExtension filename of
    ".toml"      -> decodeTomlConfig srcFile
    ".json"      -> decodeJsonConfig srcFile
    '.' : format -> reportFatal
      $ Message (FileSpan srcFile) Error
      $ "Unknown configuration file format: " ++ format
    _            -> reportFatal
      $ Message (FileSpan srcFile) Error
      $ "Missing extension. Cannot determine configuration file format."

-- | Parses a @.toml@ configuration file with the given contents.
decodeTomlConfig :: (MonadReporter r, Aeson.FromJSON a) => SrcFile -> r a
decodeTomlConfig srcFile = either (reportParsecError (mkSrcFileMap [srcFile]))
  decodeTomlDocument
  (parseTomlDoc (srcFileName srcFile) (fromString (srcFileContents srcFile)))
 where
  -- | Decodes a TOML document using the "Aeson" interface.
  decodeTomlDocument
    :: (MonadReporter r, Aeson.FromJSON a) => Toml.Table -> r a
  decodeTomlDocument document = case Aeson.fromJSON (Aeson.toJSON document) of
    Aeson.Error msg      -> reportFatal
      $ Message (FileSpan srcFile) Error
      $ "Invalid configuration file format: " ++ msg
    Aeson.Success result -> return result

-- | Parses a @.json@ file with the given contents.
decodeJsonConfig :: (MonadReporter r, Aeson.FromJSON a) => SrcFile -> r a
decodeJsonConfig srcFile
  = case Aeson.eitherDecode (fromString (srcFileContents srcFile)) of
    Right result  -> return result
    Left errorMsg -> reportFatal $ Message (FileSpan srcFile) Error errorMsg

-- | Encodes the given value using its "Aeson" interface and saves
--   the encoded value as @.json@ file.
saveConfig
  :: (MonadIO r, MonadReporter r, Aeson.ToJSON a) => FilePath -> a -> r ()
saveConfig filename
  = liftIO . LazyByteString.writeFile filename . Aeson.encodePretty
