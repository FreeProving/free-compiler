module Free.Instance.Identity where

open import Data.Empty using (⊥)

open import Free       using (Free)


-- Representation of the `Identity` monad using free.
Shape : Set
Shape = ⊥

Position : Shape → Set
Position _ = ⊥

Identity : Set → Set
Identity = Free Shape Position