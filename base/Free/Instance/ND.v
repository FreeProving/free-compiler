(** * Definition of the state effect in terms of the free monad. *)

From Base Require Import Free.
From Base Require Import Free.Util.Void.

Module ND.

  Definition ID : Type := (nat * nat * nat).

  Inductive Shape : Type :=
  | sfail : Shape
  | schoice : option ID -> Shape.

  Definition Pos (s : Shape) : Type :=
  match s with
  | sfail => Void
  | schoice _ => bool
  end.

  (* Type synonym and smart constructors for the non-determinism monad. *)
  Module Import Monad.
    Definition ND (A : Type) : Type := Free Shape Pos A.
   
    Definition Fail {A : Type} : ND A :=
      impure sfail (fun p : Pos sfail => match p with end).

    Definition Choice {A : Type} mid l r : ND A :=
       impure (schoice mid) (fun p : Pos (schoice mid) => if p then l else r).
  End Monad.


  (* Partial instance for the non-determinism monad. *)
  Instance Partial : Partial Shape Pos := {
      undefined := fun {A : Type}                => Fail;
      error     := fun {A : Type} (msg : string) => Fail
    }.

End ND.

(* The type and smart constructor should be visible to other modules
   but to use the shape, position function or partial instance the
   identifier must be fully qualified, e.g. [Choice.Partial]. *)
Export ND.Monad.
