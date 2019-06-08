From Base Require Import Free.

Inductive Pair
  {F : Type -> Type} (C__F : Container F)
  (A B : Type) : Type :=
  | pair_ : Free C__F A -> Free C__F B -> Pair C__F A B.

Arguments pair_ {F} {C__F} {A} {B}.

(* smart constructor *)
Definition Pair_
  {F : Type -> Type} {C__F : Container F}
  {A B : Type} (x : Free C__F A) (y : Free C__F B)
  : Free C__F (Pair C__F A B) :=
  pure (pair_ x y).
