{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains functions for loading and decoding 'Environment's
--   from TOML configuration files.
--
--   The configuaration file contains the names and types of predefined
--   functions, constructors and data types. The configuration file format
--   is TOML (see <https://github.com/toml-lang/toml>).
--   JSON files can be decoded as well. The TOML format is preferred for
--   configuration files maintained by humans and JSON should be used to
--   read automatically generated (serialized) environment configurations.
--
--   = Configuration file contents
--
--   The TOML document is expected to contain four arrays of tables @types@,
--   @type-synonyms@, @constructors@ and @functions@. Each table in these
--   arrays defines a data type, type synonym, constrcutor or function
--   respectively. The expected contents of each table is described below.
--
--   == Data types
--
--   The tables in the @types@ array must contain the following key/value pairs:
--     * @haskell-name@ (@String@) the Haskell name of the type constructor.
--     * @coq-name@ (@String@) the identifier of the corresponding Coq type
--       constructor.
--     * @arity@ (@Integer@) the number of type arguments expected by the
--       type constructor.
--
--   == Type synonyms
--
--   The tables in the @type-synonyms@ array must contain the following
--   key/value pairs:
--     * @haskell-name@ (@String@) the Haskell name of the type synonym.
--     * @coq-name@ (@String@) the identifier of the corresponding Coq
--       definition.
--     * @arity@ (@Integer@) the number of type arguments expected by the
--       type synonym.
--     * @haskell-type@ (@String@) the Haskell type that is abbreviated by
--       the type synonym.
--     * @type-arguments@ (@Array@ of @String@) the Haskell identifiers of the
--       type arguments. Must be of length @arity@.
--
--   == Constructors
--
--   The tables in the @constructors@ array must contain the following
--   key/value pairs:
--     * @haskell-type@ (@String@) the Haskell type of the data constructor.
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
--     * @haskell-type@ (@String@) the Haskell type of the function.
--     * @haskell-name@ (@String@) the Haskell name of the function.
--     * @coq-name@ (@String@) the identifier of the corresponding Coq
--       function.
--     * @arity@ (@Integer@) the number of arguments expected by the function.

module Compiler.Environment.Decoder
  ( loadEnvironment
  )
where

import           Data.Aeson                     ( (.:)
                                                , (.:?)
                                                , (.!=)
                                                )
import qualified Data.Aeson                    as Aeson
import qualified Data.Aeson.Types              as Aeson
import           Data.Char                      ( isAlphaNum )
import           Data.Maybe                     ( catMaybes )
import qualified Data.Text                     as T
import qualified Data.Vector                   as Vector

import           Compiler.Analysis.DependencyExtraction
                                                ( typeVars )
import           Compiler.Config
import qualified Compiler.Coq.AST              as G
import           Compiler.Environment
import           Compiler.Environment.Entry
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Parser
import           Compiler.Haskell.SrcSpan
import           Compiler.Haskell.Simplifier
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

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
            $   flip evalConverter emptyEnv
            $   liftReporter (parseType "<config-input>" (T.unpack txt))
            >>= simplifyType
    case res of
      Nothing -> Aeson.parserThrowError [] (showPretty ms)
      Just t  -> return t

-- | Restores an 'Environment' from the configuration file.
instance Aeson.FromJSON Environment where
  parseJSON = Aeson.withObject "Environment" $ \env -> do
    defineTypes <- env .:? "types" .!= Aeson.Array Vector.empty
      >>= Aeson.withArray "Data types" (mapM parseConfigType)
    defineTypeSyns <- env .:? "type-synonyms" .!= Aeson.Array Vector.empty
      >>= Aeson.withArray "Type Synonyms" (mapM parseConfigTypeSyn)
    defineCons  <- env .:? "constructors" .!= Aeson.Array Vector.empty
      >>= Aeson.withArray "Constructors" (mapM parseConfigCon)
    defineFuncs <- env .:? "functions" .!= Aeson.Array Vector.empty
      >>= Aeson.withArray "Functions" (mapM parseConfigFunc)
    return
      (foldr
        ($)
        emptyEnv
        (  Vector.toList defineTypes
        ++ Vector.toList defineTypeSyns
        ++ Vector.toList defineCons
        ++ Vector.toList defineFuncs
        )
      )
   where
    parseConfigType :: Aeson.Value -> Aeson.Parser (Environment -> Environment)
    parseConfigType = Aeson.withObject "Data type" $ \obj -> do
      arity       <- obj .: "arity"
      haskellName <- obj .: "haskell-name"
      coqName     <- obj .: "coq-name"
      return $ addEntry haskellName DataEntry
        { entrySrcSpan = NoSrcSpan
        , entryArity = arity
        , entryIdent = coqName
        }

    parseConfigTypeSyn
      :: Aeson.Value
      -> Aeson.Parser (Environment -> Environment)
    parseConfigTypeSyn = Aeson.withObject "Type synonym" $ \obj -> do
      arity       <- obj .: "arity"
      typeSyn     <- obj .: "haskell-type"
      typeArgs    <- obj .: "type-arguments"
      haskellName <- obj .: "haskell-name"
      coqName     <- obj .: "coq-name"
      return $ addEntry haskellName TypeSynEntry
        { entrySrcSpan = NoSrcSpan
        , entryArity = arity
        , entryTypeArgs = typeArgs
        , entryTypeSyn = typeSyn
        , entryIdent = coqName
        }

    parseConfigCon :: Aeson.Value -> Aeson.Parser (Environment -> Environment)
    parseConfigCon = Aeson.withObject "Constructor" $ \obj -> do
      arity                  <- obj .: "arity"
      haskellName            <- obj .: "haskell-name"
      haskellType            <- obj .: "haskell-type"
      coqName                <- obj .: "coq-name"
      coqSmartName           <- obj .: "coq-smart-name"
      let (argTypes, returnType) = HS.splitType haskellType arity
      return $ addEntry haskellName ConEntry
        { entrySrcSpan = NoSrcSpan
        , entryArity = arity
        , entryArgTypes = argTypes
        , entryReturnType = returnType
        , entryIdent = coqName
        , entrySmartIdent = coqSmartName
        }

    parseConfigFunc :: Aeson.Value -> Aeson.Parser (Environment -> Environment)
    parseConfigFunc = Aeson.withObject "Function" $ \obj -> do
      arity       <- obj .: "arity"
      haskellName <- obj .: "haskell-name"
      haskellType <- obj .: "haskell-type"
      coqName     <- obj .: "coq-name"
      let (argTypes, returnType) = HS.splitType haskellType arity
      return $ addEntry haskellName FuncEntry
        { entrySrcSpan  = NoSrcSpan
        , entryArity    = arity
        , entryTypeArgs =
            catMaybes $ map HS.identFromName $ typeVars haskellType
        , entryArgTypes = argTypes
        , entryReturnType = returnType
        , entryIdent = coqName
        }

-- | Loads an environment configuration file from a @.toml@ or @.json@ file.
loadEnvironment :: FilePath -> ReporterIO Environment
loadEnvironment = loadConfig
