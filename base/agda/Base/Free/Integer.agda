module Base.Free.Integer where

open import Data.Nat                   using (zero; suc)
open import Data.Integer               using (+_; -_) renaming (ℤ to ℤᵖ; _+_ to _+ᵖ_; _-_ to _-ᵖ_; _*_ to _*ᵖ_)
open import Data.Integer.Properties    using (_≤?_; _<?_) renaming (_≟_ to _≟ᵖ_)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- for literals
open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Agda.Builtin.FromNat       public

open import Base.Free                  using (Free; pure; impure; _>>=_)
open import Base.Partial               using (Partial; error)
open import Base.Free.Bool             using (𝔹; not)
open import Base.Free.Unit             using (⊤ᵖ)


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

_≟_ : ∀ {S P} → Free S P (ℤ S P) → Free S P (ℤ S P) → Free S P (𝔹 S P)
mx ≟ my = mx >>= λ x → my >>= λ y → pure ⌊ x ≟ᵖ y ⌋

_≠_ : ∀ {S P} → Free S P (ℤ S P) → Free S P (ℤ S P) → Free S P (𝔹 S P)
mx ≠ my = not (mx ≟ my)
instance
  number : Number ℤᵖ
  number = record
    { Constraint = λ _ → ⊤ᵖ
    ; fromNat    = λ n → + n
    }

  negative : Negative ℤᵖ
  negative = record
    { Constraint = λ _ → ⊤ᵖ
    ; fromNeg    = λ n → - (+ n)
    }

-- If it encounters a negative exponent the Haskell implementation of @(^)@ raises an exception using @errorWithoutStackTrace@.
_^_ : ∀ {S P} → ⦃ Partial S P ⦄ → Free S P (ℤ S P) → Free S P (ℤ S P) → Free S P (ℤ S P)
mx ^ pure (+ 0)         = pure 1
mx ^ pure (+ (suc n))   = mx * (mx ^ (pure (+ n)))
mx ^ pure (ℤᵖ.negsuc n) = error "*** Exception: Negative exponent"
mx ^ impure s pf        = impure s pf
