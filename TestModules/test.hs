module Test where
{-
Testfälle für bisherige Funktion des Compilers
-}

data Bool =
  B_True
  |B_False

data Maybe a =
  Nothing
  | Just a

data Identity a = Identity a

data Either a b =
  Left a
  | Right b

newtype Fd = Fd1 Int


data List' a =
  Nil'
  | Cons' a (List' a)

data Tree a =
  Leaf
  | Branch a (Tree a) (Tree a)

plus :: Int -> Int -> Int
plus a b = a + b

minus :: Int -> Int -> Int
minus a b = a - b

not :: Bool -> Bool
not b = case b of
  False -> True
  True -> False

head :: [a] -> a
head list = case list of
     (x : xs) -> x

sillyFun1 :: [a] -> [a]
sillyFun1 list = case list of
    (x : xs) -> [x]

sillyFun2 :: Bool -> [a] -> [a]
sillyFun2 b xs = case b of
    True -> xs
    False -> sillyFun1 xs

null :: [a] -> Bool
null list = case list of
  [] -> True
  _ -> False
{-}
--type Queue a = List a
-}
data Test =
  T1 Int
  | T2 String


append :: [a] -> [a] -> [a]
append xs ys  = case xs of
  [] -> ys
  (z : zs) -> z : append zs ys

reverse_ :: [a] -> [a]
reverse_ xs = case xs of
  [] -> []
  (y : ys) -> append (reverse_ ys) [y]

concat_ :: [[a]] -> [a]
concat_ xs = case xs of
  [] -> []
  (y : ys) -> append y (concat_ ys)

length' :: [a] -> Int
length' xs = case xs of
      [] -> 0
      (y : ys) -> plus 1 (length' ys)

indexLength :: [a] -> Int
indexLength xs = minus (length' xs) 1

ifTest :: Bool -> Int
ifTest b =
  if b == True
    then 1
    else 2

doAppend :: [a] -> [a] -> [a]
doAppend xs ys = append xs ys

ifTest2 :: Bool -> [a] -> [a]
ifTest2 b xs =
  if b == True
    then append xs []
    else []

intersperseOne :: [Int] -> [Int]
intersperseOne xs =
  1 : case xs of
           [] -> []
           (y : ys)  -> y : intersperseOne ys

-- Does not currently work with helper-function transformation
intersperse :: a -> [a] -> [a]
intersperse sep xs = case xs of
    [] -> []
    (y : ys) ->  y : case ys of
               [] -> []
               _  -> sep : intersperse sep ys


map' :: (a -> b) -> [a] -> [b]
map' f xs = case xs of
  [] -> []
  (y : ys) -> f y : map' f ys

-- Does not currently work with helper-function transformation
filter' :: (a -> Bool) -> [a] -> [a]
filter' p xs = case xs of
    [] -> []
    (y : ys) -> if p y
                  then y : filter' p ys
                  else filter' p ys

foldr' :: (a -> b -> b) -> b -> [a] -> b
foldr' f e xs = case xs of
  [] -> e
  (y : ys) -> f y (foldr' f e ys)

foldl' :: (b -> a -> b) -> b -> [a] -> b
foldl' f e xs = case xs of
  [] -> e
  (y : ys) -> foldl' f (f e y) ys

scanl' :: (b -> a -> b) -> b -> [a] -> [b]
scanl' f e xs = case xs of
  [] -> [e]
  (y : ys) -> e : scanl' f (f e y) ys
