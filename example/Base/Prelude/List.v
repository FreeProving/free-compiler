From Base Require Import Free.

Inductive List
  {F : Type -> Type} (C__F : Container F)
  (A : Type) : Type :=
  | Nil  : List C__F A
  | Cons : Free C__F A -> Free C__F (List C__F A) -> List C__F A.

Arguments Nil  {F} {C__F} {A}.
Arguments Cons {F} {C__F} {A}.
