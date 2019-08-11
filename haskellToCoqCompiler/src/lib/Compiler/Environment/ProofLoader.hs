{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains functions for loading Coq proofs for translated
--   QuickCheck properties from a TOML configuration file.
--
--   = Configuration file format
--
--   The configuration file format is TOML (for more information see
--   <https://github.com/toml-lang/toml>).
--
--   The configuration file contains one table for every QuickCheck property.
--   The name of the table must be the same as the Haskell QuickCheck property.
--   The following key/value pairs are allowed in such tables:
--
--     * @proof@ (@String@, required) a (multiline) string that contains the
--       tactics to apply, i.e. everything that stands between @Proof.@ and
--       @Qed.@ (both exclusive) in a Coq proof.
--     * @admitted@ (@Boolean@, optional) whether the proof is not finished
--       yet. if set to @true@, @Admitted.@ will be used instead of @Qed.@ at
--       the end of the proof. The default value is @false@, i.e. @Qed.@
--       will be used.

module Compiler.Environment.ProofLoader
  ( loadProofs
  )
where

import           Data.Aeson                     ( (.:)
                                                , (.:?)
                                                , (.!=)
                                                )
import qualified Data.Aeson                    as Aeson
import qualified Data.Aeson.Types              as Aeson
import qualified Data.HashMap.Strict           as HashMap
import qualified Data.Map.Strict               as Map
import           Data.Map.Strict                ( Map )
import qualified Data.Text                     as T

import           Compiler.Config
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Reporter

-- | Maps the names of Haskell QuickCheck properties to the corresponding
--   Coq 'Proof's.
newtype Proofs = Proofs (Map HS.Name G.Proof)

-- | Restores a Coq proof from the configuration file.
instance Aeson.FromJSON G.Proof where
  parseJSON = Aeson.withObject "Proof" $ \proof -> do
    tacticsString <- proof .: "proof"
    admitted <- proof .:? "admitted" .!= False
    let tactics = T.stripEnd (T.pack tacticsString)
    if admitted
      then return (G.ProofAdmitted tactics)
      else return (G.ProofQed tactics)

-- | Restores Coq proofs from the configuration file.
instance Aeson.FromJSON Proofs where
  parseJSON = Aeson.withObject "Proofs" $ \document -> do
    entries <- mapM (uncurry parseEntry) (HashMap.toList document)
    return (Proofs (Map.fromList entries))
   where
    parseEntry :: T.Text -> Aeson.Value -> Aeson.Parser (HS.Name, G.Proof)
    parseEntry key value = do
      let name = HS.Ident (T.unpack key)
      proof <- Aeson.parseJSON value
      return (name, proof)

-- | Loads Coq proofs for translated QuickCheck properties from a `.toml`
--   configuration file.
loadProofs :: FilePath -> ReporterIO (Map HS.Name G.Proof)
loadProofs filename = do
  Proofs proofs <- loadConfig filename
  return proofs
