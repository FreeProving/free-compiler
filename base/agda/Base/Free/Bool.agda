module Base.Free.Bool where

open import Data.Bool using (Bool; true; false) renaming (_∧_ to _∧ᵖ_; _∨_ to _∨ᵖ_)
open import Base.Free using (Free; pure; _>>=_)

𝔹 : (Shape : Set) → (Shape → Set) → Set
𝔹 _ _ = Bool

True : ∀ {S P} → Free S P (𝔹 S P)
True = pure true

False : ∀ {S P} → Free S P (𝔹 S P)
False = pure false

_∧_ : ∀ {S P} → Free S P (𝔹 S P) → Free S P (𝔹 S P) → Free S P (𝔹 S P)
mx ∧ my = mx >>= λ x → my >>= λ y → pure (x ∧ᵖ y)

_∨_ : ∀ {S P} → Free S P (𝔹 S P) → Free S P (𝔹 S P) → Free S P (𝔹 S P)
mx ∨ my = mx >>= λ x → my >>= λ y → pure (x ∨ᵖ y)
