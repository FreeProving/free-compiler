-- | This module contains the definition of the data type that is used
--   by the 'FreeC.Environment.Environment' to distinguish the type
--   and value name spaces.

module FreeC.Environment.Scope where

import qualified FreeC.IR.Syntax               as HS

-- | In Haskell type and function names live in separate scopes. Therefore we
--   need to qualify each name stored in the 'FreeC.Environment.Environment'
--   with the scope it is defined in.
data Scope = TypeScope | ValueScope
  deriving (Eq, Ord, Show)

-- | Type that is used by maps in the 'FreeC.Environment.Environment' to
--   qualify Haskell names with the scopes they are defined in.
type ScopedName = (Scope, HS.QName)
