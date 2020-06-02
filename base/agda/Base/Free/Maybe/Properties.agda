<<<<<<< HEAD:base/agda/Base/Free/Maybe/Properties.agda

module Base.Free.Maybe.Properties where

open import Relation.Binary.PropositionalEquality using (refl; cong)

open import Base.Free                             using (Free; pure; impure)
open import Base.Free.Maybe                       using (Just; Nothing)      renaming (Maybe to MaybeF)
=======
module Free.Instance.Maybe.Properties where

open import Relation.Binary.PropositionalEquality using (refl; cong)

open import Free                                  using (Free; pure; impure)
open import Free.Instance.Maybe                   using (Just; Nothing)      renaming (Maybe to MaybeF)
>>>>>>> dev-agda:base/agda/Free/Instance/Maybe/Properties.agda

open import Base.Isomorphism                      using (_≃_)
open        _≃_
open import Base.Extensionality                   using (∀-extensionality)


-- The usual `Maybe` monad representation an the free version are isomorphic.
data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

Maybe≃MaybeF : ∀ {A} → Maybe A ≃ MaybeF A
to Maybe≃MaybeF (just x) = Just x
to Maybe≃MaybeF nothing  = Nothing
from Maybe≃MaybeF (pure x)      = just x
from Maybe≃MaybeF (impure tt _) = nothing
from∘to Maybe≃MaybeF (just x) = refl
from∘to Maybe≃MaybeF nothing  = refl
to∘from Maybe≃MaybeF (pure x)      = refl
to∘from Maybe≃MaybeF (impure tt x) = cong (impure tt) (∀-extensionality λ())
