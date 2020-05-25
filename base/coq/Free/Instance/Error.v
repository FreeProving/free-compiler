(** * Definition of the error monad in terms of the free monad. *)

From Base Require Import Free.

Module Error.
  (* TODO Container instance that corresponds to [Const]. *)
  (* Definition Shape : Type := (* ... *). *)
  (* Definition Pos (s : Shape) : Type := (* ... *). *)

  (* TODO Type synonym and smart constructors for the error monad. *)
  Module Import Monad.

  End Monad.

  (* TODO Partial instance for the error monad. *)
End Error.

(* The type and smart constructor should be visible to other modules
   but to use the shape or position function the identifier must be
   fully qualified, i.e. [Error.Partial]. *)
Export Error.Monad.
