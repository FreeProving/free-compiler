From Base Require Import Free.Monad.

(** Convenience class for handling effectful programs. *)
Class Handler (Shape : Type) (Pos : Shape -> Type) (A B : Type) := {
  handle : Free Shape Pos A -> B
}.

