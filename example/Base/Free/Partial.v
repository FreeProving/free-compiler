From Base Require Import Free.Container.
From Base Require Import Free.Monad.

Require Import Coq.Strings.String.

Class Partial (F : Type -> Type) :=
  {
    C__F      : Container F;
    undefined : forall {A : Type}, Free C__F A;
    error     : forall {A : Type}, string -> Free C__F A
  }.
