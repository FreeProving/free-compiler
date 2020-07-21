module Base.Prelude.Bool where

open import Data.Bool using (Bool; true; false; if_then_else_) renaming (_∧_ to _∧ᵖ_; _∨_ to _∨ᵖ_; not to notᵖ)
open import Base.Free using (Free; pure; _>>=_)

𝔹 : (Shape : Set) → (Shape → Set) → Set
𝔹 _ _ = Bool

True : ∀ {S P} → Free S P (𝔹 S P)
True = pure true

False : ∀ {S P} → Free S P (𝔹 S P)
False = pure false

_∧_ : ∀ {S P} → Free S P (𝔹 S P) → Free S P (𝔹 S P) → Free S P (𝔹 S P)
mx ∧ my = mx >>= λ x → if x then my else False

_∨_ : ∀ {S P} → Free S P (𝔹 S P) → Free S P (𝔹 S P) → Free S P (𝔹 S P)
mx ∨ my = mx >>= λ x → if x then True else my

not : ∀ {S P} → Free S P (𝔹 S P) → Free S P (𝔹 S P)
not mb = mb >>= λ b → pure (notᵖ b)
