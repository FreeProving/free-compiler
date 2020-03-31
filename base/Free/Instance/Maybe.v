(** * Definition of the maybe monad in terms of the free monad. *)

Require Import Coq.Strings.String.

From Base Require Import Free.
From Base Require Import Free.Util.Void.

Module Maybe.
  (* Container instance for a functor [One] with exactly one element. *)
  Definition Shape : Type := unit.
  Definition Pos (s : Shape) : Type := Void.

  (* Type synonym and smart constructors for the maybe monad. *)
  Module Import Monad.
    Definition Maybe (A : Type) : Type := Free Shape Pos A.
    Definition Just {A : Type} (x : A) : Maybe A := pure x.
    Definition Nothing {A : Type} : Maybe A :=
      impure tt (fun (p : Pos tt) => match p with end).
  End Monad.

  (* Partial instance for the maybe monad. *)
  Instance Partial : Partial Shape Pos := {
      undefined := fun {A : Type}                => Nothing;
      error     := fun {A : Type} (msg : string) => Nothing
    }.
End Maybe.

(* The type and smart constructor should be visible to other modules
   but to use the shape, position function or partial instance the
   identifier must be fully qualified, i.e. [Maybe.Partial]. *)
Export Maybe.Monad.
