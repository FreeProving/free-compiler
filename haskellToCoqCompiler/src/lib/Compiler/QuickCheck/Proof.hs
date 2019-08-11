-- | This module contains data types for representing Coq proofs for
--   translated QuickCheck properties (See "Compiler.Converter.QuickCheck").

module Compiler.QuickCheck.Proof where

-- | Represents a Coq proof for a translated QuickCheck property.
data Proof = Proof
  { tactics :: String -- ^ The Coq tactics to apply.
  , admitted :: Bool  -- ^ Whether the proof still need to be completed.
  }
 deriving Show

-- | An admitted proof with only a placeholder text.
blankProof :: Proof
blankProof = Proof {tactics = "  (* FILL IN HERE *)", admitted = True}
