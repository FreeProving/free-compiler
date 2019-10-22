-- | This module contains utility functions for logical connectives of
--   boolean predicates.

module Compiler.Util.Predicate where

import           Control.Monad
import           Control.Monad.Reader           ( )

-- | Conjunction of two boolean predicates.
(.&&.) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(.&&.) = liftM2 (&&)

-- | Disjunction of two boolean predicates.
(.||.) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(.||.) = liftM2 (||)

infixr 3 .&&.
infixr 2 .||.
