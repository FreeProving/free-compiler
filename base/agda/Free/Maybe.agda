module Free.Maybe where

open import Data.Unit  using (⊤; tt)
open import Data.Empty using (⊥)

open import Free       using (Free; pure; impure)


-- representation of the maybe monad using Free
Shape = ⊤

Position : Shape → Set
Position _ = ⊥

Maybe : Set → Set
Maybe = Free Shape Position

Nothing : ∀ {A} → Maybe A
Nothing = impure tt λ()

Just : ∀ {A} → A → Maybe A
Just x = pure x