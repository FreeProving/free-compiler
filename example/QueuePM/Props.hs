module QueuePM.Props where

import           Test.QuickCheck

import           QueuePM.Queue
import           QueuePM.QueueI
import           QueuePM.Util

invariant :: QueueI a -> Bool
invariant (f, b) = null b || not (null f)

prop_inv_empty :: Bool
prop_inv_empty = invariant emptyI

prop_inv_add :: a -> QueueI a -> Property
prop_inv_add x q = invariant q ==> property (invariant (addI x q))

-------------------------------------------------------------------------------

toQueue :: QueueI a -> Queue a
toQueue (f, b) = f `append` reverse b

prop_isEmpty :: QueueI a -> Property
prop_isEmpty qi = invariant qi ==> isEmptyI qi === isEmpty (toQueue qi)

prop_add :: a -> QueueI a -> Property
prop_add x qi = toQueue (addI x qi) === add x (toQueue qi)

prop_front :: QueueI a -> Property
prop_front qi =
  invariant qi && not (isEmptyI qi) ==> frontI qi === front (toQueue qi)
