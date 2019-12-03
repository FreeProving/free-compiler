{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains functions for loading and decoding 'ModuleInterface's
--   from TOML configuration files.
--
--   The module interface file contains exported entries of the 'Environment'.
--   The file format is TOML (see <https://github.com/toml-lang/toml>).
--   JSON files can be decoded as well. The TOML format is preferred for
--   configuration files maintained by humans and JSON should be used to
--   read automatically generated (serialized) interfaces.
--
--   = File contents
--
--   The TOML document is expected to contain four arrays of tables @types@,
--   @type-synonyms@, @constructors@ and @functions@. Each table in these
--   arrays defines a data type, type synonym, constrcutor or function
--   respectively. The expected contents of each table is described below.
--   In addition, the module interface file contains meta information in the
--   top-level table.
--
--   == Top-Level
--
--   The top-level table must contain the following key/value pairs:
--     * @module-name@ (@String@) the name of the module that is described by
--       the module interface file.
--
--   == Data types
--
--   The tables in the @types@ array must contain the following key/value pairs:
--     * @haskell-name@ (@String@) the qualified Haskell name of the type
--       constructor in the module it has been defined in.
--     * @coq-name@ (@String@) the identifier of the corresponding Coq type
--       constructor.
--     * @arity@ (@Integer@) the number of type arguments expected by the
--       type constructor.
--
--   == Type synonyms
--
--   The tables in the @type-synonyms@ array must contain the following
--   key/value pairs:
--     * @haskell-name@ (@String@) the qualified Haskell name of the type
--       synonym in the module it has been defined in.
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
--     * @haskell-name@ (@String@) the qualified Haskell name of the data
--       constructor in the module it has been defined in.
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
--     * @haskell-name@ (@String@) the qualified Haskell name of the function
--       in the module it has been defined in.
--     * @coq-name@ (@String@) the identifier of the corresponding Coq
--       function.
--     * @arity@ (@Integer@) the number of arguments expected by the function.
--     * @partial@ (@Boolean@) whether the function is partial (i.e., requires
--       an instance of the @Partial@ type class).

module Compiler.Environment.Decoder
  ( loadModuleInterface
  )
where

import           Data.Aeson                     ( (.:)
                                                , (.:?)
                                                , (.!=)
                                                )
import qualified Data.Aeson                    as Aeson
import qualified Data.Aeson.Types              as Aeson
import           Data.Maybe                     ( catMaybes )
import qualified Data.Set                      as Set
import qualified Data.Text                     as T
import qualified Data.Vector                   as Vector
import           Text.RegexPR

import           Compiler.Analysis.DependencyExtraction
                                                ( typeVars )
import           Compiler.Config
import qualified Compiler.Coq.AST              as G
import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Parser
import           Compiler.Haskell.SrcSpan
import           Compiler.Haskell.Simplifier
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-- | All Haskell names in the interface file are qualified.
instance Aeson.FromJSON HS.QName where
  parseJSON = Aeson.withText "HS.QName" $ \txt -> do
    let str   = T.unpack txt
        regex = "^(\\w+(\\.\\w+)*)\\.(\\w+|\\([^\\(\\)]*\\))$"
    case matchRegexPR regex str of
      Just (_, ms) -> do
        let Just modName = lookup 1 ms
            Just name = lookup 3 ms
        return (HS.Qual modName (parseName name))
      m -> Aeson.parserThrowError [] ("Invalid Haskell name " ++ str ++ " " ++ show m)
   where
    parseName :: String -> HS.Name
    parseName ('(':sym) = HS.Symbol (take (length sym - 1) sym)
    parseName ident     = HS.Ident ident

-- | Restores a Coq identifier from the interface file.
instance Aeson.FromJSON G.Qualid where
  parseJSON = Aeson.withText "G.Qualid" $ return . G.bare . T.unpack

-- | Restores a Haskell type from the interface file.
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
instance Aeson.FromJSON ModuleInterface where
  parseJSON = Aeson.withObject "ModuleInterface" $ \env -> do
    modName <- env .: "module-name"
    exportedTypes <- env .: "exported-types"
    exportedValues <- env .: "exported-values"
    types <- env .:? "types" .!= Aeson.Array Vector.empty
      >>= Aeson.withArray "Data types" (mapM parseConfigType)
    typeSyns <- env .:? "type-synonyms" .!= Aeson.Array Vector.empty
      >>= Aeson.withArray "Type Synonyms" (mapM parseConfigTypeSyn)
    cons  <- env .:? "constructors" .!= Aeson.Array Vector.empty
      >>= Aeson.withArray "Constructors" (mapM parseConfigCon)
    funcs <- env .:? "functions" .!= Aeson.Array Vector.empty
      >>= Aeson.withArray "Functions" (mapM parseConfigFunc)
    return ModuleInterface
      { interfaceModName = modName
      , interfaceExports = Set.fromList
        (  map ((,) TypeScope)  exportedTypes
        ++ map ((,) ValueScope) exportedValues
        )
      , interfaceEntries = Set.fromList
        (  Vector.toList types
        ++ Vector.toList typeSyns
        ++ Vector.toList cons
        ++ Vector.toList funcs
        )
      }
   where
    parseConfigType :: Aeson.Value -> Aeson.Parser EnvEntry
    parseConfigType = Aeson.withObject "Data type" $ \obj -> do
      arity       <- obj .: "arity"
      haskellName <- obj .: "haskell-name"
      coqName     <- obj .: "coq-name"
      return DataEntry
        { entrySrcSpan = NoSrcSpan
        , entryArity   = arity
        , entryIdent   = coqName
        , entryName    = haskellName
        }

    parseConfigTypeSyn :: Aeson.Value -> Aeson.Parser EnvEntry
    parseConfigTypeSyn = Aeson.withObject "Type synonym" $ \obj -> do
      arity       <- obj .: "arity"
      typeSyn     <- obj .: "haskell-type"
      typeArgs    <- obj .: "type-arguments"
      haskellName <- obj .: "haskell-name"
      coqName     <- obj .: "coq-name"
      return TypeSynEntry
        { entrySrcSpan  = NoSrcSpan
        , entryArity    = arity
        , entryTypeArgs = typeArgs
        , entryTypeSyn  = typeSyn
        , entryIdent    = coqName
        , entryName     = haskellName
        }

    parseConfigCon :: Aeson.Value -> Aeson.Parser EnvEntry
    parseConfigCon = Aeson.withObject "Constructor" $ \obj -> do
      arity        <- obj .: "arity"
      haskellName  <- obj .: "haskell-name"
      haskellType  <- obj .: "haskell-type"
      coqName      <- obj .: "coq-name"
      coqSmartName <- obj .: "coq-smart-name"
      let (argTypes, returnType) = HS.splitType haskellType arity
      return ConEntry
        { entrySrcSpan    = NoSrcSpan
        , entryArity      = arity
        , entryArgTypes   = argTypes
        , entryReturnType = returnType
        , entryIdent      = coqName
        , entrySmartIdent = coqSmartName
        , entryName = haskellName
        }

    parseConfigFunc :: Aeson.Value -> Aeson.Parser EnvEntry
    parseConfigFunc = Aeson.withObject "Function" $ \obj -> do
      arity       <- obj .: "arity"
      haskellName <- obj .: "haskell-name"
      haskellType <- obj .: "haskell-type"
      partial     <- obj .: "partial"
      coqName     <- obj .: "coq-name"
      let (argTypes, returnType) = HS.splitType haskellType arity
          typeArgs = catMaybes $ map HS.identFromQName $ typeVars haskellType
      return FuncEntry
        { entrySrcSpan       = NoSrcSpan
        , entryArity         = arity
        , entryTypeArgs      = typeArgs
        , entryArgTypes      = argTypes
        , entryReturnType    = returnType
        , entryNeedsFreeArgs = True
        , entryIsPartial     = partial
        , entryIdent         = coqName
        , entryName          = haskellName
        }

-- | Loads an module interface file from a @.toml@ or @.json@ file.
loadModuleInterface :: FilePath -> ReporterIO ModuleInterface
loadModuleInterface = loadConfig
