module Base.Prelude.List where

open import Size      using (Size; ↑_)
open import Base.Free using (Free; pure)

data List (Shape : Set) (Pos : Shape → Set) (A : Set) : {Size} → Set where
  cons : ∀ {i : Size} → Free Shape Pos A → Free Shape Pos (List Shape Pos A {i}) → List Shape Pos A {↑ i}
  nil  : List Shape Pos A

pattern Cons mx mxs = pure (cons mx mxs)
pattern Nil         = pure nil
