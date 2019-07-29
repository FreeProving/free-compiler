From Base Require Import Free.

Section SecList.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).

  Inductive List (A : Type) : Type :=
    | nil  : List A
    | cons : Free' A -> Free' (List A) -> List A.

  Arguments nil  {A}.
  Arguments cons {A}.

  (* smart constructors *)

  Definition Nil {A : Type} : Free' (List A) := pure nil.

  Definition Cons {A : Type} (x : Free' A) (xs : Free' (List A))
    : Free' (List A) :=
    pure (cons x xs).

End SecList.

Arguments nil  {Shape} {Pos} {A}.
Arguments cons {Shape} {Pos} {A}.
