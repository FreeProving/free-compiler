(** * Constructs and helper functions needed for sharing *)

(* Type synonym for a sharing id *)
Definition ID : Type := (nat * nat * nat).

Set Implicit Arguments.
(* Helper function to construct a triple from a pair and a single value *)
Definition tripl A B C (p : A * B) (c : C) : A * B * C :=
  let '(a,b) := p in (a,b,c).
