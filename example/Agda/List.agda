module List where
  open import Base.Free
  open import Base.Partial
  open import Base.Prelude
  zip :
    ∀ {Shape} {Pos} {a} {b} {i} →
    Free Shape Pos (List Shape Pos a {i}) →
    Free Shape Pos (List Shape Pos b) →
    Free Shape Pos (List Shape Pos (Pair Shape Pos a b))
  zip xs ys
    = xs >>=
      λ xs₁ →
        case xs₁ of
        λ { nil → Nil
          ; (cons x xs')
              → ys >>=
                λ ys₁ →
                  case ys₁ of
                  λ { nil → Nil ; (cons y ys') → Cons (Pair′ x y) (zip xs' ys') }
          }
  unzip :
    ∀ {Shape} {Pos} {a} {b} {i} →
    Free Shape Pos (List Shape Pos (Pair Shape Pos a b) {i}) →
    Free Shape Pos
    (Pair Shape Pos (List Shape Pos a) (List Shape Pos b))
  unzip xys
    = xys >>=
      λ xys₁ →
        case xys₁ of
        λ { nil → Pair′ Nil Nil
          ; (cons xy xys')
              → xy >>=
                λ xy₁ →
                  case xy₁ of
                  λ { (pair x y)
                        → unzip xys' >>=
                          λ f → case f of λ { (pair xs ys) → Pair′ (Cons x xs) (Cons y ys) }
                    }
          }
  tail :
    ∀ {Shape} {Pos} {a} →
    ⦃ Partial Shape Pos ⦄ →
    Free Shape Pos (List Shape Pos a) →
    Free Shape Pos (List Shape Pos a)
  tail xs
    = xs >>=
      λ xs₁ →
        case xs₁ of
        λ { nil → error "tail: empty list" ; (cons x xs') → xs' }
  reverse' :
    ∀ {Shape} {Pos} {a} {i} →
    Free Shape Pos (List Shape Pos a) →
    Free Shape Pos (List Shape Pos a {i}) →
    Free Shape Pos (List Shape Pos a)
  reverse' acc xs
    = xs >>=
      λ xs₁ →
        case xs₁ of
        λ { nil → acc ; (cons x xs') → reverse' (Cons x acc) xs' }
  reverse :
    ∀ {Shape} {Pos} {a} →
    Free Shape Pos (List Shape Pos a) →
    Free Shape Pos (List Shape Pos a)
  reverse x = reverse' Nil x
  null :
    ∀ {Shape} {Pos} {a} →
    Free Shape Pos (List Shape Pos a) → Free Shape Pos (𝔹 Shape Pos)
  null xs
    = xs >>=
      λ xs₁ → case xs₁ of λ { nil → True ; (cons x xs') → False }
  map :
    ∀ {Shape} {Pos} {a} {b} {i} →
    Free Shape Pos (Free Shape Pos a → Free Shape Pos b) →
    Free Shape Pos (List Shape Pos a {i}) →
    Free Shape Pos (List Shape Pos b)
  map f xs
    = xs >>=
      λ xs₁ →
        case xs₁ of
        λ { nil → Nil
          ; (cons x xs') → Cons (f >>= λ f₁ → f₁ x) (map f xs')
          }
  length :
    ∀ {Shape} {Pos} {a} {i} →
    Free Shape Pos (List Shape Pos a {i}) →
    Free Shape Pos (ℤ Shape Pos)
  length xs
    = xs >>=
      λ xs₁ →
        case xs₁ of
        λ { nil → pure 0 ; (cons x xs') → (pure 1 + length xs') }
  intersperse :
    ∀ {Shape} {Pos} {a} {i} →
    Free Shape Pos a →
    Free Shape Pos (List Shape Pos a {i}) →
    Free Shape Pos (List Shape Pos a)
  intersperse sep xs
    = xs >>=
      λ xs₁ →
        case xs₁ of
        λ { nil → Nil
          ; (cons y ys)
              → Cons y
                (ys >>=
                 λ ys₁ →
                   case ys₁ of
                   λ { nil → Nil ; (cons z zs) → Cons sep (intersperse sep ys) })
          }
  head :
    ∀ {Shape} {Pos} {a} →
    ⦃ Partial Shape Pos ⦄ →
    Free Shape Pos (List Shape Pos a) → Free Shape Pos a
  head xs
    = xs >>=
      λ xs₁ →
        case xs₁ of λ { nil → error "head: empty list" ; (cons x xs') → x }
  foldr :
    ∀ {Shape} {Pos} {a} {b} {i} →
    Free Shape Pos
    (Free Shape Pos a →
     Free Shape Pos (Free Shape Pos b → Free Shape Pos b)) →
    Free Shape Pos b →
    Free Shape Pos (List Shape Pos a {i}) → Free Shape Pos b
  foldr f e xs
    = xs >>=
      λ xs₁ →
        case xs₁ of
        λ { nil → e
          ; (cons x xs') → f >>= λ f₁ → f₁ x >>= λ f₂ → f₂ (foldr f e xs')
          }
  foldr1 :
    ∀ {Shape} {Pos} {a} →
    ⦃ Partial Shape Pos ⦄ →
    Free Shape Pos
    (Free Shape Pos a →
     Free Shape Pos (Free Shape Pos a → Free Shape Pos a)) →
    Free Shape Pos (List Shape Pos a) → Free Shape Pos a
  foldr1 f xs
    = xs >>=
      λ xs₁ →
        case xs₁ of
        λ { nil → error "foldr1: empty list"
          ; (cons x xs') → foldr f x xs'
          }
  maximum :
    ∀ {Shape} {Pos} →
    ⦃ Partial Shape Pos ⦄ →
    Free Shape Pos (List Shape Pos (ℤ Shape Pos)) →
    Free Shape Pos (ℤ Shape Pos)
  maximum x
    = foldr1
      (pure λ a → pure λ b → (a ≥ b) >>= λ f → if f then a else b) x
  minimum :
    ∀ {Shape} {Pos} →
    ⦃ Partial Shape Pos ⦄ →
    Free Shape Pos (List Shape Pos (ℤ Shape Pos)) →
    Free Shape Pos (ℤ Shape Pos)
  minimum x
    = foldr1
      (pure λ a → pure λ b → (a ≤ b) >>= λ f → if f then a else b) x
  or :
    ∀ {Shape} {Pos} →
    Free Shape Pos (List Shape Pos (𝔹 Shape Pos)) →
    Free Shape Pos (𝔹 Shape Pos)
  or x = foldr (pure λ x₁ → pure λ x₂ → (x₁ ∨ x₂)) False x
  product :
    ∀ {Shape} {Pos} →
    Free Shape Pos (List Shape Pos (ℤ Shape Pos)) →
    Free Shape Pos (ℤ Shape Pos)
  product x = foldr (pure λ x₁ → pure λ x₂ → (x₁ * x₂)) (pure 1) x
  sum :
    ∀ {Shape} {Pos} →
    Free Shape Pos (List Shape Pos (ℤ Shape Pos)) →
    Free Shape Pos (ℤ Shape Pos)
  sum x = foldr (pure λ x₁ → pure λ x₂ → (x₁ + x₂)) (pure 0) x
  foldl :
    ∀ {Shape} {Pos} {b} {a} {i} →
    Free Shape Pos
    (Free Shape Pos b →
     Free Shape Pos (Free Shape Pos a → Free Shape Pos b)) →
    Free Shape Pos b →
    Free Shape Pos (List Shape Pos a {i}) → Free Shape Pos b
  foldl f e xs
    = xs >>=
      λ xs₁ →
        case xs₁ of
        λ { nil → e
          ; (cons x xs') → foldl f (f >>= λ f₁ → f₁ e >>= λ f₂ → f₂ x) xs'
          }
  append :
    ∀ {Shape} {Pos} {a} {i} →
    Free Shape Pos (List Shape Pos a {i}) →
    Free Shape Pos (List Shape Pos a) →
    Free Shape Pos (List Shape Pos a)
  append xs ys
    = xs >>=
      λ xs₁ →
        case xs₁ of λ { nil → ys ; (cons x xs') → Cons x (append xs' ys) }
  concat :
    ∀ {Shape} {Pos} {a} →
    Free Shape Pos (List Shape Pos (List Shape Pos a)) →
    Free Shape Pos (List Shape Pos a)
  concat x = foldr (pure λ x₁ → pure λ x₂ → append x₁ x₂) Nil x
  and :
    ∀ {Shape} {Pos} →
    Free Shape Pos (List Shape Pos (𝔹 Shape Pos)) →
    Free Shape Pos (𝔹 Shape Pos)
  and x = foldr (pure λ x₁ → pure λ x₂ → (x₁ ∧ x₂)) True x
