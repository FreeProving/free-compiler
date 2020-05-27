module Free.Instance.Maybe where

open import Data.Unit  using (⊤; tt)
open import Data.Empty using (⊥)

open import Free       using (Free; pure; impure)


-- Representation of the `Maybe` monad using Free.
Shape : Set
Shape = ⊤

Position : Shape → Set
Position _ = ⊥

Maybe : Set → Set
Maybe = Free Shape Position

Nothing : ∀ {A} → Maybe A
Nothing = impure tt λ()

Just : ∀ {A} → A → Maybe A
Just x = pure x
