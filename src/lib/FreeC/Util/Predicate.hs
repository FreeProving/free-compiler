-- | This module contains utility functions for logical connectives of
--   boolean predicates.

module FreeC.Util.Predicate where

import           Control.Monad
import           Control.Monad.Reader           ( )

-- | Combines two predicates to a new predicate whose result is the conjunction
--   of the results of the two given predicates.
(.&&.) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(.&&.) = liftM2 (&&)

-- | Combines two predicates to a new predicate whose result is the disjunction
--   of the results of the two given predicates.
(.||.) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(.||.) = liftM2 (||)

infixr 3 .&&.
infixr 2 .||.
