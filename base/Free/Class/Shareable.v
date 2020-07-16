From Base Require Import Free.Monad.

Class Shared (Shape : Type) (Pos : Shape -> Type) :=
  {
    share : forall {A : Type}, Free Shape Pos A -> Free Shape Pos (Free Shape Pos A)
  }.
