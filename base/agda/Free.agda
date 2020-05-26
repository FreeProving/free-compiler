module Free where

-- free monad over shapes S and positions P
data Free (S : Set) (P : S → Set) (A : Set) : Set where
  pure : A → Free S P A

  impure : (s : S) → (pf : P s → Free S P A) → Free S P A

infixl 1 _>>=_
_>>=_ : {S : Set} {P : S → Set} {A : Set} {B : Set} → Free S P A → (A → Free S P B) → Free S P B
pure   x    >>= k = k x
impure s pf >>= k = impure s λ p → pf p >>= k

infixl 4 _⊛_
_⊛_ : ∀ {S P A B} → Free S P (A → B) → Free S P A → Free S P B
mf ⊛ mx = mf >>= λ f → mx >>= λ x → pure (f x)

liftA2 : ∀ {S P A B C} → (A → B → C) → (Free S P A → Free S P B → Free S P C)
liftA2 f x y = pure f ⊛ x ⊛ y