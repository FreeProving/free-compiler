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
import           Data.Maybe                     ( catMaybes )

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
        $ catMaybes
        $ map (uncurry (uncurry (const encodeEntry)))
        $ Map.assocs
        $ Map.filter p
        $ exportedEntries env

-- | Encodes an entry of the environment with the given name.
encodeEntry :: HS.QName -> EnvEntry -> Maybe Aeson.Value
encodeEntry (HS.Qual _ _) _ = Nothing
encodeEntry (HS.UnQual name) entry
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
  haskellName = Aeson.toJSON (showPretty name)

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

-- | Serializes an environment and writes it to a @.json@ file.
writeEnvironment :: FilePath -> Environment -> ReporterIO ()
writeEnvironment = saveConfig
