module FreeC.Util.SnocList where

-- | Reversed version of @[]@.
--
--   (internal) implementation taken from Edward A. Kmett's @folds@ package.
data SnocList a = Snoc (SnocList a) a | Nil deriving (Eq, Ord, Show, Read)

instance Functor SnocList where
  fmap f (Snoc xs x) = Snoc (fmap f xs) (f x)
  fmap _ Nil         = Nil
  {-# INLINABLE fmap #-}

instance Foldable SnocList where
  foldl f z m0 = go m0   where
    go (Snoc xs x) = f (go xs) x
    go Nil         = z
  {-# INLINE foldl #-}
  foldMap f (Snoc xs x) = foldMap f xs `mappend` f x
  foldMap _ Nil         = mempty
  {-# INLINABLE foldMap #-}

instance Traversable SnocList where
  traverse f (Snoc xs x) = Snoc <$> traverse f xs <*> f x
  traverse _ Nil         = pure Nil
  {-# INLINABLE traverse #-}
