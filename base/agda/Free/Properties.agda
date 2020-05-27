module Free.Properties where

open import Relation.Binary.PropositionalEquality using (_≢_)

open import Free                                  using (Free; pure; impure)

discriminate : ∀ {S P A} {s : S} {pf : P s → Free S P A} {a : A} → impure s pf ≢ pure a
discriminate = λ ()
