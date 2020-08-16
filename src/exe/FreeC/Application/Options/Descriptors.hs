-- | This module contains descriptors for the command line options that are
--   understood by the command line option parser
--   (see "FreeC.Application.Options.Parser").
module FreeC.Application.Options.Descriptors where

import           System.Console.GetOpt

import           FreeC.Application.Options
import           FreeC.Backend
import           FreeC.Frontend

-- | The command line option descriptors from the @GetOpt@ library for the
--   command line options understood by the command line option parser.
optionDescriptors :: [OptDescr (Options -> Options)]
optionDescriptors
  = [ Option ['h'] ["help"] (NoArg (\opts -> opts { optShowHelp = True }))
        "Display this message."
    , Option ['v'] ["version"] (NoArg (\opts -> opts { optShowVersion = True }))
        "Print version information."
    , Option ['o'] ["output"]
        (ReqArg (\p opts -> opts { optOutputDir  = Just p
                                 , optImportDirs = p : optImportDirs opts
                                 }) "DIR")
        (unlines [ "Optional. Path to output directory."
                 , "Prints to the console by default."
                 ])
    , Option ['i'] ["import"]
        (ReqArg (\p opts -> opts { optImportDirs = p : optImportDirs opts })
         "DIR")
        (unlines
         [ "Optional. Adds the specified directory to the search path for"
         , "imported modules. The compiler looks in the current and output"
         , "directory by default. Multiple import directories can be added"
         , "by specifying additional `--import` options."
         ])
    , Option ['b'] ["base-library"]
        (ReqArg (\p opts -> opts { optBaseLibDir = p }) "DIR")
        (unlines
         [ "Optional. Path to directory that contains the compiler's Coq"
         , "Base library. By default the compiler will look for the Base"
         , "library in it's data directory."
         ])
    , Option [] ["no-coq-project"]
        (NoArg (\opts -> opts { optCreateCoqProject = False }))
        (unlines
         [ "Disables the creation of a `_CoqProject` file in the output"
         , "directory. If the `--output` option is missing or the"
         , "`_CoqProject` file exists already, no `_CoqProject` is created."
         ])
    , Option [] ["no-agda-lib"]
        (NoArg (\opts -> opts { optCreateAgdaLib = False }))
        (unlines [ "Disables the creation of an `.agda-lib` file in the output"
                 , "directory. If the `--output` option is missing or the"
                 , "`.agda-lib` file exists already, no `.agda-lib` is created."
                 ])
    , Option [] ["transform-pattern-matching"]
        (NoArg (\opts -> opts { optTransformPatternMatching = True }))
        (unlines
         [ "Experimental. Enables the automatic transformation of pattern"
         , "matching, including guard elimination and case completion."
         , "If this option is enabled, no location information will be"
         , "available in error messages."
         ])
    , Option [] ["dump-transformed-modules"]
        (ReqArg (\p opts -> opts { optDumpTransformedModulesDir = Just p })
         "DIR")
        (unlines
         [ "If `--transform-pattern-matching` is enabled, the transformed"
         , "Haskell modules will be placed in the given directory."
         , "This option adds location information to error messages that"
         , "refer to the dumped file."
         ])
    , Option [] ["from"] (ReqArg (\p opts -> opts { optFrontend = p }) "LANG")
        (unlines [ "Optional. Specifies the frontend for the compiler to use."
                 , "Allowed values are: " ++ showFrontends ++ "."
                 , "Defaults to: `" ++ defaultFrontend ++ "`."
                 ])
    , Option [] ["to"] (ReqArg (\p opts -> opts { optBackend = p }) "LANG")
        (unlines [ "Optional. Specifies the backend for the compiler to use."
                 , "Allowed values are: " ++ showBackends ++ "."
                 , "Defaults to: `" ++ defaultBackend ++ "`."
                 ])
    ]
