Module Monad.

Set Implicit Arguments.
Set Maximal Implicit Insertion.


Definition o_return (A : Type) : A -> option A :=
  Some.

Definition o_bind (A B : Type) (m : option A) (f : A -> option B) : option B :=
  match m with
  | None => None
  | Some A => f A
  end.


Notation "m >>= f" := (o_bind m f) (left associativity, at level 50).

Inductive identity (A : Type) : Type :=
  | Ident : A -> identity A.

Definition i_return (A : Type) : A -> identity A :=
 Ident.

Definition i_bind (A B : Type) ( m : identity A) (f : A -> identity B) : identity B :=
  match m with
  |Ident A => f A
  end.

Notation "m >>=' f" := (i_bind m f) (left associativity, at level 50).

Inductive List (A : Type) : Type := 
  | Nil : List A
  | Cons : option A -> option (List A) -> List A.

Arguments Nil {A}.

Definition singleton (A : Type) (ox : option A) :=
  o_return (Cons ox (o_return Nil)).

Inductive Pair (A B :Type) : Type := 
  | P : option A -> option B -> Pair A B.


Notation "a || b" := (or a b) (left associativity, at level 50).

End Monad.
