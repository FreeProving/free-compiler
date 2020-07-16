module Base.Prelude.Pair where

open import Base.Free using (Free; pure)

data Pair (Shape : Set) (Pos : Shape → Set) (A B : Set) : Set where
  pair : Free Shape Pos A → Free Shape Pos B → Pair Shape Pos A B

pattern Pair′ ma mb = pure (pair ma mb)
