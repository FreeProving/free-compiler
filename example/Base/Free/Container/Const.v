(** * Container instance for the error monad. *)

Inductive Const (B A : Type) : Type :=
  | const : B -> Const B A.

(* TODO *)
