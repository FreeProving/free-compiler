Module Monad.

Set Implicit Arguments.
Set Maximal Implicit Insertion.


Definition return_ (A : Type) : A -> option A :=
  Some.

Definition bind_ (A B : Type) (m : option A) (f : A -> option B) : option B :=
  match m with
  | None => None
  | Some A => f A
  end.


Notation "m >>= f" := (bind_ m f) (left associativity, at level 50).

Inductive List (A : Type) : Type := 
  | Nil : List A
  | Cons : option A -> option (List A) -> List A.

Arguments Nil {A}.

Definition singleton (A : Type) (ox : option A) :=
  return_ (Cons ox (return_ Nil)).

Inductive Pair (A B :Type) : Type := 
  | P : option A -> option B -> Pair A B.

End Monad.
