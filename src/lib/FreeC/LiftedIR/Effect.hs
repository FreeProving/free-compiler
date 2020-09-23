-- | This module contains a data type for effect constraints.
module FreeC.LiftedIR.Effect where

-- | An effect constraint.
--
--   These effects corresponds to type classes constraining the container used
--   by the @Free@ monad. The order of the constructors in this data type
--   determines the order of constraints in the generated function declarations.
data Effect = Sharing | Partiality | Tracing | Normalform
 deriving ( Eq, Ord, Read, Show )
