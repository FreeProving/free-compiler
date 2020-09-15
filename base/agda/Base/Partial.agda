module Base.Partial where

open import Data.String using (String)

open import Base.Free   using (Free)

record Partial (S : Set) (P : S → Set) : Set₁ where
  field
    undefined : {A : Set} → Free S P A
    error     : {A : Set} → String → Free S P A
open Partial ⦃ ... ⦄ public
