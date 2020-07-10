module Base.Free.Unit where

open import Data.Unit using (tt)         renaming (⊤ to ⊤ᵖ) public
open import Base.Free using (Free; pure)

⊤ : (S : Set) (P : S → Set) → Set
⊤ _ _ = ⊤ᵖ

pattern Tt = pure tt
