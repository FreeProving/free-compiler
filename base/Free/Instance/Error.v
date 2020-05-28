(** * Definition of the error monad in terms of the free monad. *)

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

  (* TODO Partial instance for the error monad. *)
End Error.

(* The type and smart constructor should be visible to other modules
   but to use the shape or position function the identifier must be
   fully qualified, i.e. [Error.Partial]. *)
Export Error.Monad.
