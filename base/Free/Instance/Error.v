(** * Definition of the error monad in terms of the free monad. *)

Require Import Coq.Strings.String.

From Base Require Import Free.
From Base Require Import Free.Util.Void.

Module Error.
  (* Container instance that corresponds to [Const]. *)
  Definition Shape (E : Type) : Type := E.
  Definition Pos {E : Type} (s : Shape E) : Type := Void.

  (* Type synonym and smart constructors for the error monad. *)
  Module Import Monad.
    Definition Error (E A : Type) := Free (Shape E) Pos A.
    Definition NoError {E A : Type} (x : A) : Error E A := pure x.
    Definition ThrowError {E A : Type} (msg : E) : Error E A :=
      impure msg (fun (p : Pos msg) => match p with end).
  End Monad.

  (* Partial instance for the error monad. *)
  Open Scope string_scope.
  Instance Partial : Partial  (Shape string) Pos := {
    undefined := fun {A : Type}                => ThrowError "undefined";
    error     := fun {A : Type} (msg : string) => ThrowError msg
  }.
  Close Scope string_scope.
End Error.

(* The type and smart constructor should be visible to other modules
   but to use the shape or position function the identifier must be
   fully qualified, i.e. [Error.Partial]. *)
Export Error.Monad.
