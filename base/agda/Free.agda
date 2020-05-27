module Free where

-- free monad over shapes S and positions P
data Free (S : Set) (P : S → Set) (A : Set) : Set where
  pure : A → Free S P A

  impure : (s : S) → (pf : P s → Free S P A) → Free S P A

infixl 1 _>>=_
_>>=_ : {S : Set} {P : S → Set} {A : Set} {B : Set} → Free S P A → (A → Free S P B) → Free S P B
pure   x    >>= k = k x
impure s pf >>= k = impure s λ p → pf p >>= k
