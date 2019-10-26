{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains functions for encoding 'Environment's in JSON
--   and writing them to @.json@ files.
--
--   See "Compiler.Environemt.Decoder" for the configuration file format.
--   Encoding environments as TOML files is not supported, since TOML is
--   intended for human maintained configuration files only.

module Compiler.Environment.Encoder
  ( writeEnvironment
  )
where

import           Data.Aeson                     ( (.=) )
import qualified Data.Aeson                    as Aeson
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromJust )

import           Compiler.Config
import           Compiler.Environment
import           Compiler.Environment.Entry
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-- | Serializes an 'Environment'.
--
--   The environment must only contain top level entries (i.e., there must be
--   no entries for variables or type variables).
instance Aeson.ToJSON Environment where
  toJSON env = Aeson.object
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
        $ map (uncurry (uncurry (const encodeEntry)))
        $ filter (p . snd)
        $ Map.assocs
        $ Map.map fst
        $ envEntries env

-- | Encodes an entry of the environment with the given name.
encodeEntry :: HS.Name -> EnvEntry -> Aeson.Value
encodeEntry name entry
  | isDataEntry entry = Aeson.object
    ["haskell-name" .= haskellName, "coq-name" .= coqName, "arity" .= arity]
  | isTypeSynEntry entry = Aeson.object
    [ "haskell-name" .= haskellName
    , "coq-name" .= coqName
    , "arity" .= arity
    , "haskell-type" .= typeSyn
    , "type-arguments" .= typeArgs
    ]
  | isConEntry entry = Aeson.object
    [ "haskell-type" .= haskellType
    , "haskell-name" .= haskellName
    , "coq-name" .= coqName
    , "coq-smart-name" .= coqSmartName
    , "arity" .= arity
    ]
  | isFuncEntry entry = Aeson.object
    [ "haskell-type" .= haskellType
    , "haskell-name" .= haskellName
    , "coq-name" .= coqName
    , "arity" .= arity
    ]
  | otherwise = error "encodeEntry: Cannot serialize (type) variable entry."
 where
  haskellName :: Aeson.Value
  haskellName = Aeson.toJSON (showPretty name)

  coqName, coqSmartName :: Aeson.Value
  coqName      = Aeson.toJSON (entryIdent entry)
  coqSmartName = Aeson.toJSON (entrySmartIdent entry)

  arity :: Aeson.Value
  arity = Aeson.toJSON (entryArity entry)

  haskellType :: Aeson.Value
  haskellType =
    let returnType = fromJust (entryReturnType entry)
        argTypes   = map fromJust (entryArgTypes entry)
        funcType   = foldr (HS.TypeFunc NoSrcSpan) returnType argTypes
    in  Aeson.toJSON (showPretty funcType)

  typeSyn :: Aeson.Value
  typeSyn = Aeson.toJSON (showPretty (entryTypeSyn entry))

  typeArgs :: Aeson.Value
  typeArgs = Aeson.toJSON (entryTypeArgs entry)

-- | Serializes an environment and writes it to a @.json@ file.
writeEnvironment :: FilePath -> Environment -> ReporterIO ()
writeEnvironment = saveConfig
