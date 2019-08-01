{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains functions for loading and decoding 'Environment's
--   from TOML configuration files.
--
--   The configuaration file contains the names and types of predefined
--   functions, constructors and data types. The configuration file format
--   is TOML (see <https://github.com/toml-lang/toml>).
--
--   = Configuration file contents
--
--   The TOML document is expected to contain three arrays of tables @types@,
--   @constructors@ and @functions@. Each table in these arrays defines a
--   Type, Constrcutor or Function respectively. The expected contents of each
--   table is described below.
--
--   == Types
--
--   The tables in the @types@ array must contain the following key/value pairs:
--     * @haskell-name@ (@String@) the Haskell name of the type constructor.
--     * @coq-name@ (@String@) the identifier of the corresponding Coq type
--       constructor.
--     * @arity@ (@Integer@) the number of type arguments expected by the
--       type constructor.
--
--   == Constructors
--
--   The tables in the @constructors@ array must contain the following
--   key/value pairs:
--     * @haskell-name@ (@String@) the Haskell name of the data constructor.
--     * @coq-name@ (@String@) the identifier of the corresponding Coq data
--       constructor.
--     * @coq-smart-name@ (@String@) the identifier of the corresponding Coq
--       smart constructor.
--     * @arity@ (@Integer@) the number of arguments expected by the data
--       constructor.
--
--   == Functions
--
--   The tables in the @functions@ array must contain the following
--   key/value pairs:
--     * @haskell-name@ (@String@) the Haskell name of the function.
--     * @coq-name@ (@String@) the identifier of the corresponding Coq
--       function.
--     * @arity@ (@Integer@) the number of arguments expected by the function.

module Compiler.Converter.EnvironmentLoader
  ( loadEnvironment
  )
where

import qualified Text.Parsec.Error             as Parsec
import qualified Text.Toml.Types               as Toml
import           Text.Toml                      ( parseTomlDoc )
import qualified Data.Aeson                    as Aeson
import qualified Data.Aeson.Types              as Aeson
import           Data.Aeson                     ( (.:) )
import           Data.Char                      ( isAlphaNum )
import qualified Data.Text                     as T
import qualified Data.Vector                   as Vector

import           Compiler.Converter.State
import qualified Compiler.Language.Coq.AST     as G
import           Compiler.Language.Haskell.Parser
import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.Language.Haskell.Simplifier
import           Compiler.Pretty
import           Compiler.Reporter
import           Compiler.SrcSpan

-- | Restores a Haskell name (symbol or identifier) from the configuration
--   file.
instance Aeson.FromJSON HS.Name where
  parseJSON = Aeson.withText "HS.Name" $ \txt -> do
    let str = T.unpack txt
    if all isIdentChar str
      then return (HS.Ident str)
      else return (HS.Symbol str)
   where
    -- | Tests whether the given character is allowed in a Haskell identifier.
    isIdentChar :: Char -> Bool
    isIdentChar c = isAlphaNum c || c == '\'' || c == '_'

-- | Restores a Coq identifier from the configuration file.
instance Aeson.FromJSON G.Qualid where
  parseJSON = Aeson.withText "G.Qualid" $ return . G.bare . T.unpack

-- | Restores a Haskell type from the configuration file.
instance Aeson.FromJSON HS.Type where
  parseJSON = Aeson.withText "HS.Type" $ \txt -> do
    let (res, ms) =
          runReporter
            $   flip evalConverter emptyEnvironment
            $   liftReporter (parseType "<config-input>" (T.unpack txt))
            >>= simplifyType
    case res of
      Nothing -> Aeson.parserThrowError [] (showPretty ms)
      Just t  -> return t

-- | Restores an 'Environment' from the configuration file.
instance Aeson.FromJSON Environment where
  parseJSON = Aeson.withObject "Environment" $ \env -> do
    defineTypes <- env .: "types" >>= Aeson.withArray "Types" (mapM parseType)
    defineCons  <- env .: "constructors" >>= Aeson.withArray "Constructors"
                                                             (mapM parseCon)
    defineFuncs <- env .: "functions" >>= Aeson.withArray "Functions"
                                                          (mapM parseFunc)
    return
      (foldr
        ($)
        emptyEnvironment
        (  Vector.toList defineTypes
        ++ Vector.toList defineCons
        ++ Vector.toList defineFuncs
        )
      )
   where
    parseType :: Aeson.Value -> Aeson.Parser (Environment -> Environment)
    parseType = Aeson.withObject "Type" $ \obj -> do
      arity       <- obj .: "arity"
      haskellName <- obj .: "haskell-name"
      coqName     <- obj .: "coq-name"
      return (defineTypeCon haskellName arity coqName)

    parseCon :: Aeson.Value -> Aeson.Parser (Environment -> Environment)
    parseCon = Aeson.withObject "Constructor" $ \obj -> do
      arity                  <- obj .: "arity"
      haskellName            <- obj .: "haskell-name"
      haskellType            <- obj .: "haskell-type"
      coqName                <- obj .: "coq-name"
      coqSmartName           <- obj .: "coq-smart-name"
      let (argTypes, returnType) = HS.splitType haskellType arity
      return (defineCon haskellName coqName coqSmartName argTypes returnType)

    parseFunc :: Aeson.Value -> Aeson.Parser (Environment -> Environment)
    parseFunc = Aeson.withObject "Function" $ \obj -> do
      arity       <- obj .: "arity"
      haskellName <- obj .: "haskell-name"
      haskellType <- obj .: "haskell-type"
      coqName     <- obj .: "coq-name"
      let (argTypes, returnType) = HS.splitType haskellType arity
      return (defineFunc haskellName coqName argTypes returnType)

-- | Loads an environment configuration file.
loadEnvironment :: FilePath -> ReporterIO Environment
loadEnvironment filename = reportIOErrors $ do
  contents <- lift $ readFile filename
  case parseTomlDoc filename (T.pack contents) of
    Right document   -> hoist $ decodeEnvironment document
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

-- | Creates an 'Environment' that is encoded by the given TOML document.
decodeEnvironment :: Toml.Table -> Reporter Environment
decodeEnvironment document = case result of
  Aeson.Error msg -> do
    report $ Message NoSrcSpan Info $ show (Aeson.toJSON document)
    reportFatal
      $  Message NoSrcSpan Error
      $  "Invalid configuration file format: "
      ++ msg
  Aeson.Success env -> return env
 where
  result :: Aeson.Result Environment
  result = Aeson.fromJSON (Aeson.toJSON document)
