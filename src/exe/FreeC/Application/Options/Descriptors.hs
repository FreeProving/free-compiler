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
optionDescriptors :: [ OptDescr (Options -> Options) ]
optionDescriptors
  = [ Option [ 'h' ] [ "help" ] (NoArg (\opts -> opts { optShowHelp = True }))
        "Display this message."
    , Option [ 'v' ] [ "version" ]
        (NoArg (\opts -> opts { optShowVersion = True }))
        "Print version information."
    , Option [ 'o' ] [ "output" ]
        (ReqArg (\p opts -> opts { optOutputDir  = Just p
                                 , optImportDirs = p : optImportDirs opts
                                 }) "DIR")
        ("Optional. Path to output directory.\n"
         ++ "Prints to the console by default.")
    , Option [ 'i' ] [ "import" ]
        (ReqArg (\p opts -> opts { optImportDirs = p : optImportDirs opts })
         "DIR")
        ("Optional. Adds the specified directory to the search path for\n"
         ++ "imported modules. The compiler looks in the current and output\n"
         ++ "directory by default. Multiple import directories can be added\n"
         ++ "by specifying additional `--import` options.")
    , Option [ 'b' ] [ "base-library" ]
        (ReqArg (\p opts -> opts { optBaseLibDir = p }) "DIR")
        ("Optional. Path to directory that contains the compiler's Coq\n"
         ++ "Base library. By default the compiler will look for the Base\n"
         ++ "library in it's data directory.")
    , Option [] [ "no-coq-project" ]
        (NoArg (\opts -> opts { optCreateCoqProject = False }))
        ("Disables the creation of a `_CoqProject` file in the output\n"
         ++ "directory. If the `--output` option is missing or the `_CoqProject`\n"
         ++ "file exists already, no `_CoqProject` is created.\n")
    , Option [] [ "no-agda-lib" ]
        (NoArg (\opts -> opts { optCreateAgdaLib = False }))
        ("Disables the creation of an `.agda-lib` file in the output\n"
         ++ "directory. If the `--output` option is missing or the `.agda-lib`\n"
         ++ "file exists already, no `.agda-lib` is created.\n")
    , Option [] [ "transform-pattern-matching" ]
        (NoArg (\opts -> opts { optTransformPatternMatching = True }))
        ("Experimental. Enables the automatic transformation of pattern\n"
         ++ "matching, including guard elimination and case completion.\n"
         ++ "If this option is enabled, no location information will be\n"
         ++ "available in error messages.")
    , Option [] [ "dump-transformed-modules" ]
        (ReqArg (\p opts -> opts { optDumpTransformedModulesDir = Just p })
         "DIR")
        ("If `--transform-pattern-matching` is enabled, the transformed\n"
         ++ "Haskell modules will be placed in the given directory.\n"
         ++ "This option adds location information to error messages that\n"
         ++ "refer to the dumped file.")
    , Option [] [ "from" ] (ReqArg (\p opts -> opts { optFrontend = p }) "LANG")
        ("Optional. Specifies the frontend for the compiler to use.\n"
         ++ "Allowed values are: " ++ showFrontends ++ ".\nDefaults to: `"
         ++ defaultFrontend ++ "`.")
    , Option [] [ "to" ] (ReqArg (\p opts -> opts { optBackend = p }) "LANG")
        ("Optional. Specifies the backend for the compiler to use.\n"
         ++ "Allowed values are: " ++ showBackends ++ ".\nDefaults to: `"
         ++ defaultBackend ++ "`.")
    ]
