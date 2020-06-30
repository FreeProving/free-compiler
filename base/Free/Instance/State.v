(** * Definition of the state effect in terms of the free monad. *)

From Base Require Import Free.

Module State.

  Variable S : Type.
  Inductive Shape : Type := 
    | sget : Shape
    | sput : S -> Shape.
  Definition Pos (s : Shape) : Type :=
    match s with
    | sget   => S
    | sput _ => unit
    end.

  (* Type synonym and smart constructors for the state monad. *)
  Module Import Monad.
    Definition State (A : Type) : Type := Free Shape Pos A.
    (* TODO: Implement smart constructors *)
    (*Definition Get {A : Type} : State A := 
      .
    Definition Put (s : S) : State () := 
      .
    *)
  End Monad.

End State.

(* The type and smart constructor should be visible to other modules
   but to use the shape, position function or partial instance the
   identifier must be fully qualified, i.e. [State.Monad]. *)
Export State.Monad.
