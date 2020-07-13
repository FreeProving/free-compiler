module Base.Free.Instance.Maybe.Properties where

open import Relation.Binary.PropositionalEquality using (refl; cong)

open import Base.Free                             using (Free; pure; impure; _>>=_)
open import Base.Free.Instance.Maybe              using (Just; Nothing)             renaming (Maybe to MaybeF)

open import Base.Isomorphism                      using (_≃_)
open        _≃_
open import Base.Extensionality                   using (ext)

open import Data.Unit                             using (tt)
import      Relation.Binary.PropositionalEquality as Eq
open        Eq                                    using (_≡_; refl; cong)


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
to∘from Maybe≃MaybeF (impure tt x) = cong (impure tt) (ext λ())

Nothing>>=k≡Nothing : ∀ {A B} → (k : A → MaybeF B) → (Nothing >>= k) ≡ Nothing
Nothing>>=k≡Nothing k = cong (impure tt) (ext  (λ ()))
