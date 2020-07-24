From Base Require Import Free.Monad.
Require Export Coq.Strings.String.

Class Traceable (Shape : Type) (Pos : Shape -> Type) :=
  {
    trace : forall {A : Type}, string -> Free Shape Pos A -> Free Shape Pos A
  }.
