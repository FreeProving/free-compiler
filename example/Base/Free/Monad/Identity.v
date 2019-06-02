(** * Definition of the identity monad using the free monad. *)

From Base Require Import Free.Monad.
From Base Require Import Free.Container.Zero.

Definition Identity (A : Type) : Type := Free C__Zero A.
Definition Id {A : Type} (x : A) : Identity A := pure x.
