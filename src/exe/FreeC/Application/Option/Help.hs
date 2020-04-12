-- | This module contains the implementation of the @--help@ command.

module FreeC.Application.Option.Help
  ( usageHeader
  , putUsageInfo
  )
where

import           System.Console.GetOpt
import           System.Environment             ( getProgName )

import           FreeC.Application.Options.Descriptors

-- | The header of the help message.
--
--   This text is added before the description of the command line arguments.
usageHeader :: FilePath -> String
usageHeader progName =
  "Usage: "
    ++ progName
    ++ " [options...] <input-files...>\n\n"
    ++ "Command line options:"

-- | Prints the help message for the compiler.
--
--   The help message is displayed when the user specifies the @--help@ option
--   or there are no input files.
putUsageInfo :: IO ()
putUsageInfo = do
  progName <- getProgName
  putStrLn (usageInfo (usageHeader progName) optionDescriptors)
