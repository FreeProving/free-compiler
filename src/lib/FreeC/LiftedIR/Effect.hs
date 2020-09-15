-- | This module contains a data type for effect constraints.
module FreeC.LiftedIR.Effect where

-- | An effect constraint.
--
--   These effects corresponds to type classes constraining the container used
--   by the @Free@ monad.
data Effect = Partiality | Sharing
 deriving ( Show, Eq )
