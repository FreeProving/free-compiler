(** * Definition of the state effect in terms of the free monad. *)

From Base Require Import Free.

Module Share.

  (* TODO: Define Shape and Pos *)
  Inductive Shape : Type := .
  Definition Pos (s : Shape) : Type := match s with end.

  (* Type synonym and smart constructors for the state monad. *)
  Module Import Monad.
    Definition Share (A : Type) : Type := Free Shape Pos A.
   (* TODO: Add Begin and End smart constructors *)
  End Monad.

End Share.

(* The type and smart constructor should be visible to other modules
   but to use the shape, position function or partial instance the
   identifier must be fully qualified, i.e. [State.Monad]. *)
Export Share.Monad.
