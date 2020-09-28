-- This example contains definitions for the @Maybe@ data type and commonly
-- used list functions from the @Data.Maybe@ module.
module Data.Maybe where

data Maybe a = Nothing | Just a

maybe :: b -> (a -> b) -> Maybe a -> b
maybe d f mx = case mx of
  Nothing -> d
  Just x  -> f x

isJust :: Maybe a -> Bool
isJust mx = case mx of
  Nothing -> False
  Just x  -> True

isNothing :: Maybe a -> Bool
isNothing mx = case mx of
  Nothing -> True
  Just x  -> False

fromJust :: Maybe a -> a
fromJust mx = case mx of
  Nothing -> error "Maybe.fromJust: Nothing"
  Just x  -> x

fromMaybe :: a -> Maybe a -> a
fromMaybe d mx = case mx of
  Nothing -> d
  Just x  -> x

maybeToList :: Maybe a -> [a]
maybeToList mx = case mx of
  Nothing -> []
  Just x  -> [x]

listToMaybe :: [a] -> Maybe a
listToMaybe xs = case xs of
  []      -> Nothing
  x : xs' -> Just x

catMaybes :: [Maybe a] -> [a]
catMaybes mxs = case mxs of
  []        -> []
  mx : mxs' -> case mx of
    Nothing -> catMaybes mxs'
    Just x  -> x : catMaybes mxs'

mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f xs = case xs of
  []      -> []
  x : xs' -> case f x of
    Nothing -> mapMaybe f xs'
    Just y  -> y : mapMaybe f xs'
