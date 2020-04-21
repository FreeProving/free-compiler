{-# LANGUAGE TemplateHaskell #-}

-- | This module contains a template Haskell splice for reading the @VERSION@
--   file that is created by the @./tool/install.sh@ script at compile-time.

module FreeC.Application.Option.Version.VersionFile
  ( tReadVersionFile
  )
where

import           Data.List.Extra                ( trim )
import           System.IO.Error                ( catchIOError )

import           Language.Haskell.TH            ( TExp
                                                , Q
                                                , runIO
                                                )

-- | Reads the @VERSION@ file at compile-time.
--
--   The @VERSION@ file is created by the @./tool/install.sh@ script. It
--   does not exist, when the compiler is executed using the @./tool/run.sh@
--   script. In this case @Nothing@ is returned.
tReadVersionFile :: Q (TExp (Maybe String))
tReadVersionFile = do
  maybeVersion <- runIO $ readFileMaybe "VERSION"
  [|| maybeVersion ||]

-- | Like 'readFile' but returns @Nothing@ if there is an IO exception (e.g,
--   because the given file does not exist).
readFileMaybe :: FilePath -> IO (Maybe String)
readFileMaybe filename =
  (Just . trim <$> readFile filename) `catchIOError` const (return Nothing)
