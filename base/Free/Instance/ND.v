(** * Definition of the non-determinism effect in terms of the free monad. *)

From Base Require Import Free.
From Base Require Import Free.Util.Void.

Module ND.
  (* Type synonym for a choice id *)
  Definition ID : Type := (nat * nat * nat).

  (* Shape and position function *)
  Inductive Shape : Type :=
  | sfail : Shape
  | schoice : option ID -> Shape.

  Definition Pos (s : Shape) : Type :=
  match s with
  | sfail => Void
  | schoice _ => bool
  end.

  (* Type synonym and smart constructors for the non-determinism effect. *)
  Module Import Monad.
    Definition ND (A : Type) : Type := Free Shape Pos A.

    Definition Fail {A : Type} {Shape' : Type} {Pos' : Shape' -> Type} 
      `{Injectable Shape Pos Shape' Pos'} 
      : Free Shape' Pos' A :=
      impure (injS sfail) (fun p => (fun (x : Void) => match x with end) (injP p)).

    Definition Choice {A : Type} {Shape' : Type} {Pos' : Shape' -> Type} 
    `{Injectable Shape Pos Shape' Pos'} mid l r
    : Free Shape' Pos' A := 
       let s := injS (schoice mid) 
       in impure s (fun p : Pos' s => if injP p : Pos (schoice mid) then l else r).

    (** Curry notation for the choice operator *)
    Notation "x ? y" := (Choice None x y) (at level 80).
 End Monad.


  (* Partial instance for the non-determinism monad. *)
  Instance Partial : Partial Shape Pos := {
      undefined := fun {A : Type}                => Fail;
      error     := fun {A : Type} (msg : string) => Fail
    }.

End ND.


(* The type and smart constructor should be visible to other modules
   but to use the shape, position function or partial instance the
   identifier must be fully qualified, e.g. [ND.Partial]. *)
Export ND.Monad.
