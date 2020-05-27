module Extensionality where

open import Level                                 using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Postualting extensionality is consistent with agdas underlying theory.
postulate
  ∀-extensionality : ∀ {ℓ ℓ′ : Level} {A : Set ℓ} {B : A → Set ℓ′} {f g : (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g