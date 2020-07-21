module Base.Prelude.Integer where

open import Data.Nat                   using (ℕ; zero; suc)
open import Data.Integer               using (+_; -_) renaming (ℤ to ℤᵖ; _+_ to _+ᵖ_; _-_ to _-ᵖ_; _*_ to _*ᵖ_)
open import Data.Integer.Properties    using (_≤?_; _<?_) renaming (_≟_ to _≟ᵖ_)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- Imports for literals.
open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Agda.Builtin.FromNat       public

open import Base.Free                  using (Free; pure; impure; _>>=_)
open import Base.Partial               using (Partial; error)
open import Base.Prelude.Bool          using (𝔹; not)
open import Base.Prelude.Unit          using (⊤ᵖ)


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

_^ᵖ_ : ℤᵖ → ℕ → ℤᵖ
b ^ᵖ 0     = 1
b ^ᵖ suc e = b *ᵖ (b ^ᵖ e)

-- If it encounters a negative exponent the Haskell implementation of @(^)@ raises an exception using @errorWithoutStackTrace@.
_^_ : ∀ {S P} → ⦃ Partial S P ⦄ → Free S P (ℤ S P) → Free S P (ℤ S P) → Free S P (ℤ S P)
mb ^ me = me >>= λ where
  (ℤᵖ.negsuc _) → error "Negative exponent"
  (+ 0)         → pure 1
  (+ (suc e))   → mb >>= λ b → pure (b ^ᵖ suc e)

neg : ∀ {S P} → Free S P (ℤ S P) → Free S P (ℤ S P)
neg x = pure -1 * x
