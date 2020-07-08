module Base.Free.Integer where

open import Data.Unit                  using (⊤; tt) public
open import Data.Integer               using (+_; -_) renaming (ℤ to ℤᵖ; _+_ to _+ᵖ_; _-_ to _-ᵖ_; _*_ to _*ᵖ_)
open import Data.Integer.Properties    using (_≤?_; _<?_)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- for literals
open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Agda.Builtin.FromNat       public

open import Base.Free                  using (Free; pure; _>>=_)
open import Base.Free.Bool             using (𝔹)


ℤ : (Shape : Set) → (Shape → Set) → Set
ℤ _ _ = ℤᵖ

_+_ : ∀ {S P} → Free S P (ℤ S P) → Free S P (ℤ S P) → Free S P (ℤ S P)
mx + my = mx >>= λ x → my >>= λ y → pure (x +ᵖ y)

_-_ : ∀ {S P} → Free S P (ℤ S P) → Free S P (ℤ S P) → Free S P (ℤ S P)
mx - my = mx >>= λ x → my >>= λ y → pure (x -ᵖ y)

_*_ : ∀ {S P} → Free S P (ℤ S P) → Free S P (ℤ S P) → Free S P (ℤ S P)
mx * my = mx >>= λ x → my >>= λ y → pure (x *ᵖ y)

_≤_ : ∀ {S P} → Free S P (ℤ S P) → Free S P (ℤ S P) → Free S P (𝔹 S P)
mx ≤ my = mx >>= λ x → my >>= λ y → pure ⌊ x ≤? y ⌋

_<_ : ∀ {S P} → Free S P (ℤ S P) → Free S P (ℤ S P) → Free S P (𝔹 S P)
mx < my = mx >>= λ x → my >>= λ y → pure ⌊ x <? y ⌋

_>_ : ∀ {S P} → Free S P (ℤ S P) → Free S P (ℤ S P) → Free S P (𝔹 S P)
mx > my = my ≤ mx

_≥_ : ∀ {S P} → Free S P (ℤ S P) → Free S P (ℤ S P) → Free S P (𝔹 S P)
mx ≥ my = my < mx

instance
  number : Number ℤᵖ
  number = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → + n
    }

  negative : Negative ℤᵖ
  negative = record
    { Constraint = λ _ → ⊤
    ; fromNeg    = λ n → - (+ n)
    }
