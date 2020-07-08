(** * Definition of the tracing effect in terms of the free monad. *)

From Base Require Import Free.
From Base Require Import Free.Util.Void.
Require Export Coq.Strings.String.

Module Trace.

  (* Type synonym for a tracing id *)
  Definition ID : Type := nat * nat * nat.

  (* Container instance for a functor [Log]. *)
  Definition Shape : Type := option ID * string.
  Definition Pos : Shape -> Type := fun _ => unit.

  (* Type synonym and smart constructors for the maybe monad. *)
  Module Import Monad.
    Definition Trace (A : Type) : Type := Free Shape Pos A.
    Definition Nil {A : Type} (x : A) : Trace A := pure x.
    Definition LCons {A : Type} mid msg x : Trace A := 
       impure (mid, msg) (fun tt => x).

  (* Versions of the smart constructors that automatically embed values in an effect stack *)
    Definition Nil_inj {A : Type} {Shape' : Type} {Pos' : Shape' -> Type} 
      (x : A) `{Injectable Shape Pos Shape' Pos'} 
      : Free Shape' Pos' A := pure x.

    Definition LCons_inj {A : Type} {Shape' : Type} {Pos' : Shape' -> Type} 
      `{Injectable Shape Pos Shape' Pos'} mid msg x
      : Free Shape' Pos' A :=
      impure (injS (mid, msg)) (fun tt => x).
  End Monad.

  (* There is no Partial instance. *)
End Trace.

(* The type and smart constructor should be visible to other modules
   but to use the shape or position function the
   identifier must be fully qualified, i.e. [Trace.Shape]. *)
Export Trace.Monad.
