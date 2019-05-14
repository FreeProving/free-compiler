module Queue where

data List a =
  Nil
  | Cons a (List a)

data Pair a b =
  P a b

not' :: Bool -> Bool
not' b = case b of
  True -> False
  False -> True

null' :: [a] -> Bool
null' list = case list of
  [] -> True
  (_ : _ )-> False

append :: [a] -> [a] -> [a]
append xs ys  = case xs of
  [] -> ys
  (z : zs) -> (z : append zs ys)

singleton :: a -> [a]
singleton x =  x : []

reverse' :: [a] -> [a]
reverse' xs = case xs of
  [] -> []
  (y : ys) -> append (reverse' ys) (singleton y)




type Queue a = [a]

empty :: Queue a
empty = []

isEmpty :: Queue a -> Bool
isEmpty q = null' q

front :: Queue a -> a
front q = case q of
   (x : _) -> x

add :: a -> Queue a -> Queue a
add x q = append q (singleton x)

-- Definition of Queue with 2 Lists

type Queuel a = ([a] , [a])

emptyl :: Queuel a
emptyl = ([] , [])

isEmptyl :: Queuel a -> Bool
isEmptyl x = case x of
  (f , b) -> null' f

frontl :: Queuel a -> a
frontl q = case q of
  (f , b) -> case f of
    (x : xs) -> x

flipQ :: Queuel a -> Queuel a
flipQ q = case q of
  (f , b) -> case f of
        [] -> ( reverse' b, [] )
        _ -> q

addl :: a -> Queuel a -> Queuel a
addl x q = case q of
  (f , b) -> flipQ (f, x : b)


toQueue :: Queuel a -> Queue a
toQueue q = case q of
  (f, b) -> append f (reverse' b)
