From Base Require Import Free.

Inductive Pair
  {F : Type -> Type} (C__F : Container F)
  (A B : Type) : Type :=
  | Pair_ : Free C__F A -> Free C__F B -> Pair C__F A B.

Arguments Pair_ {F} {C__F} {A} {B}.
