(** * Definition of the maybe monad using the free monad. *)

From Base Require Import Free.Monad.
From Base Require Import Free.Container.
From Base Require Import Free.Container.One.

Definition Maybe (A : Type) : Type := Free C__One A.
Definition Just {A : Type} (x : A) : Maybe A := pure x.
Definition Nothing {A : Type} : Free C__One A :=
  impure (ext tt (fun (p : P__One tt) => match p with end)).
