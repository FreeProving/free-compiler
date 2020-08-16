module Queue.WithPatternMatching.QueueI where

import           Queue.WithPatternMatching.Util

type QueueI a = ( [ a ], [ a ] )

emptyI :: QueueI a
emptyI = ( [], [] )

isEmptyI :: QueueI a -> Bool
isEmptyI ( f, b ) = null f

frontI :: QueueI a -> a
frontI ( x : f, b ) = x

addI :: a -> QueueI a -> QueueI a
addI x ( f, b ) = flipQ ( f, x : b )

flipQ :: QueueI a -> QueueI a
flipQ ( [], b ) = ( reverse b, [] )
flipQ q         = q
