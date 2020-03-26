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
import qualified Compiler.Coq.AST              as G
import           Compiler.Coq.Pretty
import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.Scope
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Reporter
import           Compiler.Pretty

instance Aeson.ToJSON HS.QName where
  toJSON = Aeson.toJSON . showPretty

instance Aeson.ToJSON HS.Type where
  toJSON = Aeson.toJSON . showPretty

instance Aeson.ToJSON G.Qualid where
  toJSON = Aeson.toJSON . showPretty . PrettyCoq

-- | Serializes a 'ModuleInterface'.
instance Aeson.ToJSON ModuleInterface where
  toJSON iface = Aeson.object
    [ "module-name" .= Aeson.toJSON (interfaceModName iface)
    , "library-name" .= Aeson.toJSON (interfaceLibName iface)
    , "exported-types" .= Aeson.toJSON
      (map
        snd
        (filter ((== TypeScope) . fst) (Set.toList (interfaceExports iface)))
      )
    , "exported-values" .= Aeson.toJSON
      (map
        snd
        (filter ((== ValueScope) . fst) (Set.toList (interfaceExports iface)))
      )
    , "types" .= encodeEntriesWhere isDataEntry
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
      , "needs-free-args" .= freeArgsNeeded
      ]
  | otherwise = error "encodeEntry: Cannot serialize (type) variable entry."
 where
  haskellName :: Aeson.Value
  haskellName = Aeson.toJSON (entryName entry)

  coqName, coqSmartName :: Aeson.Value
  coqName      = Aeson.toJSON (entryIdent entry)
  coqSmartName = Aeson.toJSON (entrySmartIdent entry)

  arity :: Aeson.Value
  arity = Aeson.toJSON (entryArity entry)

  partial :: Aeson.Value
  partial = Aeson.toJSON (entryIsPartial entry)

  freeArgsNeeded :: Aeson.Value
  freeArgsNeeded = Aeson.toJSON (entryNeedsFreeArgs entry)

  maybeHaskellType :: Maybe Aeson.Value
  maybeHaskellType = do
    returnType <- entryReturnType entry
    argTypes   <- mapM id (entryArgTypes entry)
    let funcType = foldr (HS.FuncType NoSrcSpan) returnType argTypes
    return (Aeson.toJSON funcType)

  typeSyn :: Aeson.Value
  typeSyn = Aeson.toJSON (entryTypeSyn entry)

  typeArgs :: Aeson.Value
  typeArgs = Aeson.toJSON (entryTypeArgs entry)

-- | Serializes a module interface and writes it to a @.json@ file.
writeModuleInterface :: FilePath -> ModuleInterface -> ReporterIO ()
writeModuleInterface = saveConfig
