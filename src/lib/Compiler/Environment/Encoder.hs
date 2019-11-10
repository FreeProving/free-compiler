{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains functions for encoding 'ModuleInterface's in JSON
--   and writing them to @.json@ files.
--
--   See "Compiler.Environemt.Decoder" for the interface file format.
--   Encoding module interfaces as TOML files is not supported, since TOML is
--   intended for human maintained configuration files (e.g., the module
--   interface of the @Prelude@) only.

module Compiler.Environment.Encoder
  ( writeModuleInterface
  )
where

import           Data.Aeson                     ( (.=) )
import qualified Data.Aeson                    as Aeson
import           Data.Maybe                     ( catMaybes )
import qualified Data.Set                      as Set

import           Compiler.Config
import           Compiler.Environment
import           Compiler.Environment.Entry
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-- | Serializes a 'ModuleInterface'.
instance Aeson.ToJSON ModuleInterface where
  toJSON iface = Aeson.object
    [ "types" .= encodeEntriesWhere isDataEntry
    , "type-synonyms" .= encodeEntriesWhere isTypeSynEntry
    , "constructors" .= encodeEntriesWhere isConEntry
    , "functions" .= encodeEntriesWhere isFuncEntry
    ]
   where
    -- | Encodes the entries of the environment that match the given predicate.
    encodeEntriesWhere :: (EnvEntry -> Bool) -> Aeson.Value
    encodeEntriesWhere p =
      Aeson.toJSON
        $ catMaybes
        $ map encodeEntry
        $ Set.toList
        $ Set.filter p
        $ interfaceEntries iface

-- | Encodes an entry of the environment.
encodeEntry :: EnvEntry -> Maybe Aeson.Value
encodeEntry entry
  | isDataEntry entry = return $ Aeson.object
    ["haskell-name" .= haskellName, "coq-name" .= coqName, "arity" .= arity]
  | isTypeSynEntry entry = return $ Aeson.object
    [ "haskell-name" .= haskellName
    , "coq-name" .= coqName
    , "arity" .= arity
    , "haskell-type" .= typeSyn
    , "type-arguments" .= typeArgs
    ]
  | isConEntry entry = do
    haskellType <- maybeHaskellType
    return $ Aeson.object
      [ "haskell-type" .= haskellType
      , "haskell-name" .= haskellName
      , "coq-name" .= coqName
      , "coq-smart-name" .= coqSmartName
      , "arity" .= arity
      ]
  | isFuncEntry entry = do
    haskellType <- maybeHaskellType
    return $ Aeson.object
      [ "haskell-type" .= haskellType
      , "haskell-name" .= haskellName
      , "coq-name" .= coqName
      , "arity" .= arity
      , "partial" .= partial
      ]
  | otherwise = error "encodeEntry: Cannot serialize (type) variable entry."
 where
  haskellName :: Aeson.Value
  haskellName = Aeson.toJSON (showPretty (entryName entry))

  coqName, coqSmartName :: Aeson.Value
  coqName      = Aeson.toJSON (entryIdent entry)
  coqSmartName = Aeson.toJSON (entrySmartIdent entry)

  arity :: Aeson.Value
  arity = Aeson.toJSON (entryArity entry)

  partial :: Aeson.Value
  partial = Aeson.toJSON (entryIsPartial entry)

  maybeHaskellType :: Maybe Aeson.Value
  maybeHaskellType = do
    returnType <- entryReturnType entry
    argTypes   <- mapM id (entryArgTypes entry)
    let funcType = foldr (HS.TypeFunc NoSrcSpan) returnType argTypes
    return (Aeson.toJSON (showPretty funcType))

  typeSyn :: Aeson.Value
  typeSyn = Aeson.toJSON (showPretty (entryTypeSyn entry))

  typeArgs :: Aeson.Value
  typeArgs = Aeson.toJSON (entryTypeArgs entry)

-- | Serializes a module interface and writes it to a @.json@ file.
writeModuleInterface :: FilePath -> ModuleInterface -> ReporterIO ()
writeModuleInterface = saveConfig
