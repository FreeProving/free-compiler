module Compiler.NonEmptyList where

import qualified GHC.Base as B


---------------------- NonemptyList Conversions
--convert single element to nonempty list
singleton :: a -> B.NonEmpty a
singleton a =
  a B.:| []

toNonemptyList :: [a] -> B.NonEmpty a
toNonemptyList (x:xs) =
  x B.:| xs

fromNonEmptyList :: B.NonEmpty a -> [a]
fromNonEmptyList (x B.:| xs) =
  x : xs
