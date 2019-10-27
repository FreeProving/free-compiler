-- | This module defines type classes for converting between monads and their
--   monad transformer counterparts.

module Compiler.Monad.Class.Hoistable where

import           Control.Monad.Identity
import           Control.Monad.Trans.Class

-- | Type class for monad transformers whose inner monad can be lifted from
--   'Identity' to some arbitry 'Monad'.
class MonadTrans t => Hoistable t where
  -- | Lifts the transformed identity monad to any transformed monad.
  hoist :: Monad m => t Identity a -> t m a

-- | Type class for 'Hoistable' types whose 'hoist' method can be undone.
class Hoistable t => UnHoistable t where
  -- | Undoes 'hoist'.
  unhoist :: Monad m => t m a -> m (t Identity a)
