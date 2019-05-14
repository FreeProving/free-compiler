module Prelude where

data Bool = True1 | False1

and :: Bool -> Bool -> Bool
and b1 b2 = case b1 of
  False -> False
  True -> case b2 of
        False -> False
        True -> True

or :: Bool -> Bool -> Bool
or b1 b2 = case b1 of
  True -> True
  False -> case b2 of
      True -> True
      False -> False

not :: Bool -> Bool
not b = case b of
  True -> False
  False -> True

otherwise :: Bool
otherwise = True


data Maybe a = Just a | Nothing

maybe :: b -> (a -> b) -> Maybe a -> b
maybe x f mx = case mx of
  Nothing -> x
  Just y -> f y

data Either a b = Left a | Right b
-- Constructors 'Left' and 'Right' expect 2 Arguments in coq
either :: (a -> c) -> (b -> c) -> Either a b -> c
either af bf ex = case ex of
  Left a -> af a
  Right b -> bf b

data Ordering = LT | EQ | GT

fst :: (a, b) -> a
fst x = case x of
  (a, b) -> a

snd :: (a, b) -> b
snd x = case x of
  (a, b) -> b

curry :: ((a, b) -> c) -> a -> b -> c
curry f a b = f (a , b)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f p = f (fst p) (snd p)

id :: a -> a
id x = x

const :: a -> b -> a
const x y = x

flip :: ( a -> b -> c) -> b -> a -> c
flip f x y = f y x

comp :: (b -> c) -> (a -> b) -> a -> c
comp f g x = f (g x)


until :: ( a -> Bool) -> (a -> a) -> a -> a
until p f x = if p x
  then x
  else until p f (f x)
