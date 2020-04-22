{-# LANGUAGE TemplateHaskell #-}

-- | This module contains the implementation of the @--version@ command.
--
--   The template Haskell language extension is used to include the hash
--   of the Git commit at compile time.

module FreeC.Application.Option.Version where

import           Data.List                      ( intercalate )
import           Data.Version
import           GitHash
import           System.Info


import           Paths_free_compiler

-- | Prints version information for the compiler, the compiler it has been
--   compiled with and operating system it is running on.
--
--   The version string has the following format.
--
--   > The Free Compiler, version <version> (<commit>, <compiler>, <os>, <arch>)
--
--   where
--
--    * @<version>@ is the version of the compiler as specified in the
--      Cabal configuration file.
--    * @<commit>@ is the output of @git describe --always --dirty@ at
--      compile time. The output has the format @<tag>-<n>-g<hash>[-dirty]@
--      where @<tag>@ is the name of the latest tag, @<n>@ is the number of
--      commits since the latest tag, @<hash>@ is the abbreviated Git commit
--      hash and the suffix @-dirty@ is appended if there are uncommitted
--      changes.
--      If the compiler is not installed from the Git repository, this
--      information is missing.
--    * @<os>@ is the name of the operating system (e.g., "linux").
--    * @<arch>@ is the name of the machine architecture (e.g., "x86_64").
putVersionInfo :: IO ()
putVersionInfo = do
  putStrLn
    (  "The Free Compiler, version "
    ++ showVersion version
    ++ " ("
    ++ intercalate
         ", "
         (  either (const []) (return . giDescribeDirty) gitInfoOrError
         ++ [compilerName ++ " " ++ showVersion compilerVersion, os, arch]
         )
    ++ ")"
    )
 where
  -- | Compile time information about the current Git commit.
  gitInfoOrError :: Either String GitInfo
  gitInfoOrError = $$tGitInfoCwdTry

  -- | Gets the output of @git describe --always --dirty@ for the most recent
  --   commit at compile time.
  giDescribeDirty :: GitInfo -> String
  giDescribeDirty gitInfo | giDirty gitInfo = giDescribe gitInfo ++ "-dirty"
                          | otherwise       = giDescribe gitInfo
