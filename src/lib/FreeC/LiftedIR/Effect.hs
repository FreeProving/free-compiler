-- | This module contains a data type for effect constraints.
module FreeC.LiftedIR.Effect where

-- | An effect constraint.
--
--   These effects corresponds to type classes constraining the container used
--   by the @Free@ monad. The order of the constructors in this data type
--   determines the order of constraints in the generated function declarations.
--
--   The 'Sharing' effect is the first effect by convention. All other effects
--   are in alphabetical order by default.
data Effect = Sharing | Normalform | Partiality | Tracing | NonDet
 deriving ( Eq, Ord, Read, Show )
