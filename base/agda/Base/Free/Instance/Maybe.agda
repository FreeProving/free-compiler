module Base.Free.Instance.Maybe where

open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥)

open import Base.Free    using (Free; pure; impure)
open import Base.Partial using (Partial)
open        Partial


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

instance
  maybePartial : Partial Shape Position
  undefined maybePartial   = Nothing
  error     maybePartial _ = Nothing
