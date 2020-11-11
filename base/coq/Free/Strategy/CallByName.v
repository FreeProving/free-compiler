From Base Require Import Free.Monad.

Definition callByName (Shape : Type) (Pos : Shape -> Type)
  {A : Type} (p : Free Shape Pos A)
  : Free Shape Pos (Free Shape Pos A) :=
  pure p.

Notation "'shareByName'" := callByName.
