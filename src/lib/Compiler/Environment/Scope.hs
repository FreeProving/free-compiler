-- | This module contains the definition of

module Compiler.Environment.Scope where

import qualified Compiler.IR.Syntax            as HS

-- | In Haskell type and function names live in separate scopes. Therefore we
--   need to qualify each name stored in the "Compiler.Environment.Environment"
--   with the scope it is defined in.
data Scope = TypeScope | ValueScope
  deriving (Eq, Ord, Show)

-- | Type that is used by maps in the "Compiler.Environment.Environment" to
--   qualify Haskell names with the scopes they are defined in.
type ScopedName = (Scope, HS.QName)
