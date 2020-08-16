module Queue.WithoutPatternMatching.Util where

null :: [ a ] -> Bool
null xs = case xs of
  []      -> True
  x : xs' -> False

not :: Bool -> Bool
not b = case b of
  True  -> False
  False -> True

append :: [ a ] -> [ a ] -> [ a ]
append xs ys = case xs of
  []      -> ys
  x : xs' -> x : (append xs' ys)

reverse :: [ a ] -> [ a ]
reverse xs = case xs of
  []      -> []
  x : xs' -> reverse xs' `append` [x]
