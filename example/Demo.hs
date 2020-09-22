module Demo where

import Debug.Trace
import Test.QuickCheck

-- data type
data MyList a = MyNil | MyCons a (MyList a)

-- partial function
myHead :: MyList a -> a
myHead (MyCons x _) = x

-- sharing
doubleHead :: MyList Integer -> Integer
doubleHead l = myHead l + myHead l

-- traced, partial value
-- trace "First element" 1 : undefined
tracedList :: MyList Integer
tracedList = MyCons (trace "First element" 1) undefined


