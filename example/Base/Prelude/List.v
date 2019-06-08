From Base Require Import Free.

Inductive List
  {F : Type -> Type} (C__F : Container F)
  (A : Type) : Type :=
  | nil  : List C__F A
  | cons : Free C__F A -> Free C__F (List C__F A) -> List C__F A.

Arguments nil  {F} {C__F} {A}.
Arguments cons {F} {C__F} {A}.

(* smart constructors *)

Definition Nil
  {F : Type -> Type} {C__F : Container F}
  {A : Type}
  : Free C__F (List C__F A) :=
  pure (nil).

Definition Cons
  {F : Type -> Type} {C__F : Container F}
  {A : Type} (x : Free C__F A) (xs : Free C__F (List C__F A))
  : Free C__F (List C__F A) :=
  pure (cons x xs).
