From Base Require Import Free.Monad.

Definition callByName (Shape : Type) (Pos : Shape -> Type)
  {A : Type} (p : Free Shape Pos A)
  : Free Shape Pos (Free Shape Pos A) :=
  pure p.

(* When simplifying expressions, we want Coq to expand applications of
   [callByName] such that the code becomes more readable. *)
Arguments callByName Shape Pos {A} p /.
