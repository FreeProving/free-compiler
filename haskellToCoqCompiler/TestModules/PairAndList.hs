module Test where

identP :: (Int, Int) -> (Int, Int)
identP x =
  case x of
  (l, r) -> (l,r)

switch :: (a, b) -> (b, a)
switch x =
  case x of
    (a , b) -> (b , a)

identL :: [Int] -> [Int]
identL xs =
  case xs of
    [] -> []
    (x : xs) -> x : identL xs
