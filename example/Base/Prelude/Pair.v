From Base Require Import Free.

Section SecPair.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).

  Inductive Pair (A B : Type) : Type :=
    | pair_ : Free' A -> Free' B -> Pair A B.

  Arguments pair_ {A} {B}.

  (* smart constructor *)
  Definition Pair_ {A B : Type} (x : Free' A) (y : Free' B)
    : Free' (Pair A B) :=
    pure (pair_ x y).

End SecPair.

(* The arguments of the constructor and smart constructor are implicit. *)
Arguments pair_ {Shape} {Pos} {A} {B}.
Arguments Pair_ {Shape} {Pos} {A} {B}.