module Base.Free.Instance.Identity.Properties where

open import Relation.Binary.PropositionalEquality using (refl; cong)

open import Base.Free                             using (Free; pure; impure)
open import Base.Free.Instance.Identity                                      renaming (Identity to IdentityF)

open import Base.Isomorphism                      using (_≃_)
open        _≃_


-- The usual `Identity` monad representation an the free version are isomorphic.
data Identity (A : Set) : Set where
  Ident : A → Identity A

Identity≃IdentityF : ∀ {A} → Identity A ≃ IdentityF A
to Identity≃IdentityF (Ident x)  = pure x
from Identity≃IdentityF (pure x) = Ident x
from∘to Identity≃IdentityF (Ident x) = refl
to∘from Identity≃IdentityF (pure x)  = refl
