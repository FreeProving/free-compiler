{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains functions for loading and decoding 'ModuleInterface's
--   from TOML configuration files.
--
--   The module interface file contains the entries of a 'ModuleInterface'.
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
--
--     * @version@ (@Integer@) the version of the configuration file format.
--       The current version is 'moduleInterfaceFileFormatVersion'.
--       If there is a breaking change in the future, the module interface file
--       format version should be updated. The parser accepts module interface
--       files that use the most recent version only.
--     * @module-name@ (@String@) the name of the module that is described by
--       the module interface file.
--     * @library-name@ (@String@) the name of the Coq library that contains
--       the module.
--     * @exported-types@ (@Array@ of @String@) the names (@haskell-name@) of
--       the type-level entries exported by the module. All other entries in
--       the @types@ and @type-synonyms@ tables are "hidden" (i.e. cannot be
--       used by an importing module directly).
--     * @exported-values@ (@Array@ of @String@) the names (@haskell-name@) of
--       the value-level entries exported by the module. All other entries in
--       the @constructors@ and @functions@ tables are "hidden" (i.e. cannot be
--       used by an importing module directly).
--
--   == Data types
--
--   The tables in the @types@ array must contain the following key/value pairs:
--
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
--
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
--
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
--
--     * @haskell-type@ (@String@) the Haskell type of the function.
--     * @haskell-name@ (@String@) the qualified Haskell name of the function
--       in the module it has been defined in.
--     * @coq-name@ (@String@) the identifier of the corresponding Coq
--       function.
--     * @arity@ (@Integer@) the number of arguments expected by the function.
--     * @partial@ (@Boolean@) whether the function is partial (i.e., requires
--       an instance of the @Partial@ type class).
--     * @needs-free-args@ (@Boolean@) whether the arguments of the @Free@
--       monad need to be passed to the function.

module FreeC.Environment.ModuleInterface.Decoder
  ( loadModuleInterface
  )
where

import           Control.Monad                  ( when )
import           Control.Monad.IO.Class         ( MonadIO )
import           Data.Aeson                     ( (.!=)
                                                , (.:)
                                                , (.:?)
                                                )
import qualified Data.Aeson                    as Aeson
import qualified Data.Aeson.Types              as Aeson
import qualified Data.Set                      as Set
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import qualified Data.Vector                   as Vector

import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment.ModuleInterface
import           FreeC.Environment.Entry
import           FreeC.Frontend.IR.Parser
import           FreeC.IR.Reference             ( freeTypeVars )
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Reporter
import           FreeC.Pretty
import           FreeC.Util.Config

-- | The version number of the module interface file format.
--
--   Remember to keep this in sync with the version number specified in
--   "FreeC.Environment.ModuleInterface.Encoder".
--
--   We specify the version number at two different places such that if
--   a breaking change is made to the encoder or decoder, it is less likely
--   that the implementation of the corresponding change in the other module
--   is forgotten.
moduleInterfaceFileFormatVersion :: Integer
moduleInterfaceFileFormatVersion = 2

-- | Parses an IR AST node from an Aeson string.
parseAesonIR :: Parseable a => Text -> Aeson.Parser a
parseAesonIR input = do
  let srcFile   = mkSrcFile "<config-input>" (Text.unpack input)
      (res, ms) = runReporter (parseIR srcFile)
  case res of
    Nothing -> Aeson.parserThrowError [] (showPretty ms)
    Just t  -> return t

-- | All Haskell names in the interface file are qualified.
instance Aeson.FromJSON IR.QName where
  parseJSON = Aeson.withText "IR.QName" parseAesonIR

-- | Restores a Coq identifier from the interface file.
instance Aeson.FromJSON Coq.Qualid where
  parseJSON = Aeson.withText "Coq.Qualid" $ return . Coq.bare . Text.unpack

-- | Restores a Haskell type from the interface file.
instance Aeson.FromJSON IR.Type where
  parseJSON = Aeson.withText "IR.Type" parseAesonIR

-- | Restores a 'ModuleInterface' from the configuration file.
instance Aeson.FromJSON ModuleInterface where
  parseJSON = Aeson.withObject "ModuleInterface" $ \env -> do
    version <- env .: "version"
    when (version /= moduleInterfaceFileFormatVersion)
      $  Aeson.parseFail
      $  "Expected version "
      ++ show moduleInterfaceFileFormatVersion
      ++ ", got version "
      ++ show version
      ++ ".\n"
      ++ "Try to recompile the module."
    modName        <- env .: "module-name"
    libName        <- env .: "library-name"
    exportedTypes  <- env .: "exported-types"
    exportedValues <- env .: "exported-values"
    types <- env .:? "types" .!= Aeson.Array Vector.empty >>= Aeson.withArray
      "Data types"
      (mapM parseConfigType)
    typeSyns <-
      env .:? "type-synonyms" .!= Aeson.Array Vector.empty >>= Aeson.withArray
        "Type Synonyms"
        (mapM parseConfigTypeSyn)
    cons <-
      env .:? "constructors" .!= Aeson.Array Vector.empty >>= Aeson.withArray
        "Constructors"
        (mapM parseConfigCon)
    funcs <-
      env .:? "functions" .!= Aeson.Array Vector.empty >>= Aeson.withArray
        "Functions"
        (mapM parseConfigFunc)
    return ModuleInterface
      { interfaceModName = modName
      , interfaceLibName = libName
      , interfaceExports = Set.fromList
                             (  map ((,) IR.TypeScope)  exportedTypes
                             ++ map ((,) IR.ValueScope) exportedValues
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
      return DataEntry { entrySrcSpan = NoSrcSpan
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
      return TypeSynEntry { entrySrcSpan  = NoSrcSpan
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
      let (argTypes, returnType) = IR.splitFuncType haskellType arity
      return ConEntry { entrySrcSpan    = NoSrcSpan
                      , entryArity      = arity
                      , entryTypeArgs   = freeTypeVars returnType
                      , entryArgTypes   = argTypes
                      , entryReturnType = returnType
                      , entryIdent      = coqName
                      , entrySmartIdent = coqSmartName
                      , entryName       = haskellName
                      }

    parseConfigFunc :: Aeson.Value -> Aeson.Parser EnvEntry
    parseConfigFunc = Aeson.withObject "Function" $ \obj -> do
      arity          <- obj .: "arity"
      haskellName    <- obj .: "haskell-name"
      haskellType    <- obj .: "haskell-type"
      partial        <- obj .: "partial"
      freeArgsNeeded <- obj .: "needs-free-args"
      coqName        <- obj .: "coq-name"
      -- TODO this does not work with vanishing type arguments.
      let (argTypes, returnType) = IR.splitFuncType haskellType arity
          typeArgs               = freeTypeVars haskellType
      return FuncEntry { entrySrcSpan       = NoSrcSpan
                       , entryArity         = arity
                       , entryTypeArgs      = typeArgs
                       , entryArgTypes      = argTypes
                       , entryStrictArgs    = replicate arity False
                       , entryReturnType    = returnType
                       , entryNeedsFreeArgs = freeArgsNeeded
                       , entryIsPartial     = partial
                       , entryIdent         = coqName
                       , entryName          = haskellName
                       }

-- | Loads a module interface file from a @.toml@ or @.json@ file.
loadModuleInterface
  :: (MonadIO r, MonadReporter r) => FilePath -> r ModuleInterface
loadModuleInterface = loadConfig
