<<<<<<< HEAD:base/agda/Base/Free/Maybe.agda
module Base.Free.Maybe where
=======
module Free.Instance.Maybe where
>>>>>>> dev-agda:base/agda/Free/Instance/Maybe.agda

open import Data.Unit  using (⊤; tt)
open import Data.Empty using (⊥)

open import Base.Free  using (Free; pure; impure)


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
