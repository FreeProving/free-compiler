-- | This module defines type classes for converting between monads and their
--   monad transformer counterparts.

module Compiler.Monad.Class.Hoistable where

import           Control.Monad.Identity
import           Control.Monad.Trans.Class

-- | Lifts the transformed identity monad to any transformed monad.
class MonadTrans t => Hoistable t where
  hoist :: Monad m => t Identity a -> t m a

-- | Undoes 'hoist'.
class Hoistable t => UnHoistable t where
  unhoist :: Monad m => t m a -> m (t Identity a)
