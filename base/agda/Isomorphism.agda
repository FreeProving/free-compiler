module Isomorphism where

open import Relation.Binary.PropositionalEquality using (_≡_)

-- The stdlib contains @Function.Inverse@, which seems to have a similar purpose, but is more complicated.

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
