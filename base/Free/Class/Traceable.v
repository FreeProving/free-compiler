From Base Require Import Free.Monad.
Require Export Coq.Strings.String.

Class Traced (Shape : Type) (Pos : Shape -> Type) :=
  {
    trace : forall {A : Type}, string -> Free Shape Pos A -> Free Shape Pos A
  }.
