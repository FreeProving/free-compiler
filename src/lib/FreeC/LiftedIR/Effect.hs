-- | This module contains a data type for effect constraints.
module FreeC.LiftedIR.Effect where

-- | An effect constraint.
--
--   These effects corresponds to type classes constraining the container used
--   by the @Free@ monad. Currently just partiality is supported.
data Effect = Partiality
 deriving ( Show, Eq )
