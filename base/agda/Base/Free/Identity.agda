<<<<<<< HEAD:base/agda/Base/Free/Identity.agda
module Base.Free.Identity where
=======
module Free.Instance.Identity where
>>>>>>> dev-agda:base/agda/Free/Instance/Identity.agda

open import Data.Empty using (⊥)

open import Base.Free  using (Free)


-- Representation of the `Identity` monad using free.
Shape : Set
Shape = ⊥

Position : Shape → Set
Position _ = ⊥

Identity : Set → Set
Identity = Free Shape Position
