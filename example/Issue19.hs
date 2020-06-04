module Issue19 where

import           Prelude                 hiding ( const )

append :: [a] -> [a] -> b -> [a]
append xs ys = const
  (case xs of
    []      -> ys
    x : xs' -> x : (append xs' ys ())
  )

const :: a -> b -> a
const x y = x

{-

append :: [a] -> [a] -> [a]
append xs ys = case xs of
  []      -> ys
  x : xs' -> x : xs' `append` ys

append2 :: [a] -> [a] -> [a]
append2 xs = append xs

-------

append' :: [a] -> [a] -> [a]
append' !(xs :: [a]) (ys :: [a]) :: [a] = case xs of
  []      -> ys
  x : xs' -> x : xs' `append` ys

append :: [a] -> [a] -> [a]
append (xs :: [a]) (ys :: [a]) :: [a] = append' xs ys

append2 :: [a] -> [a] -> [a]
append2 (xs :: [a]) :: [a] -> [a] = \ys -> append xs ys
-}


{-

   Übersetzung in einen Testfall der obigen Haskellfunktion

   append @a @b (xs :: [a]) (ys :: [a]) :: b -> [a] = \y -> const
     (case xs of
       []      -> ys
       x : xs' -> x : (append @a @b xs' ys ())
     ) y

   Der folgende Test hingegen sollte fehlschlagen. Das okay, da man sowas in
   Haskell nicht schreiben kann.

   append @a @b (xs :: [a]) (ys :: [a]) :: b -> [a] = \y -> const
     (case xs of
       []      -> ys
       x : xs' -> x : (append @a @b xs' ys y)
     ) y

-}



append @a (xs :: [a]) (ys :: [a]) :: b -> [a] = \y -> const
  (case xs of
    []      -> ys
    x : xs' -> x : (append xs' ys ())
  ) y

---


append_0 @a !(xs :: [a]) (ys :: [a]) :: b -> [a] = \y -> const
  (case xs of
    []      -> ys
    x : xs' -> x : (append xs' ys ())
  ) y

  (\y -> const
    (xs' >>= \xs_0 -> append_0 @a xs_0 ys) y) ()


append @a (xs :: [a]) (ys :: [a]) :: b -> [a] = \y -> const
  (xs >>= \xs_0 -> append_0 @a xs_0 ys) y
