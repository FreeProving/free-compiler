From Base Require Import Free.Monad.

Require Export Coq.Strings.String.

Class Partial (Shape : Type) (Pos : Shape -> Type) :=
  {
    undefined : forall {A : Type}, Free Shape Pos A;
    error     : forall {A : Type}, string -> Free Shape Pos A
  }.
