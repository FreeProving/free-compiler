From Base Require Import Free.Monad.

Definition callByValue (Shape : Type) (Pos : Shape -> Type)
  {A : Type} (p : Free Shape Pos A)
  : Free Shape Pos (Free Shape Pos A) :=
  p >>= fun x => pure (pure x).

(* When simplifying expressions, we want Coq to expand applications of
   [callByValue] such that the code becomes more readable. *)
Arguments callByValue Shape Pos {A} p /.