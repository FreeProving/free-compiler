-- This example contains definitions for commonly used functions from
-- the @Data.Function@ module.

module Data.Function where

-- | Identity function.
id :: a -> a
id x = x

-- | @'const' x@ is a unary function which evaluates to @x@ for all inputs.
const :: a -> b -> a
const x y = x

-- | Function composition.
comp :: (b -> c) -> (a -> b) -> a -> c
comp f g x = f (g x)

infixr 9 `comp`

-- | @'flip' f@ takes its (first) two arguments in the reverse order of @f@.
flip :: (a -> b -> c) -> b -> a -> c
flip f y x = f x y

-- | Application operator.
app :: (a -> b) -> a -> b
app f x = f x

infixr 0 `app`
