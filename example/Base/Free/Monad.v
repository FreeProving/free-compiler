From Base Require Import Free.Container.

Inductive Free {F : Type -> Type} (C__F : Container F) (A : Type) : Type :=
  | pure : A -> Free C__F A
  | impure : Ext Shape Pos (Free C__F A) -> Free C__F A.

Arguments pure {F} {C__F} {A}.
Arguments impure {F} {C__F} {A}.

Section SecFree.

  Variable F : Type -> Type.
  Variable C__F : Container F.

  Section free_bind'.

    Variable A B : Type.
    Variable f: A -> Free C__F B.

    Fixpoint free_bind' (mx: Free C__F A) : Free C__F B :=
      match mx with
      | pure x => f x
      | impure e => impure (cmap free_bind' e)
      end.

  End free_bind'.

  Definition free_bind {A B : Type} (mx: Free C__F A) (f: A -> Free C__F B)
    : Free C__F B :=
    free_bind' A B f mx.

  (* TODO free return *)

End SecFree.

Arguments free_bind {F} {C__F} {A} {B}.

Notation "mx >>= f" := (free_bind mx f) (left associativity, at level 50).
