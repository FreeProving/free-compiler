From Base Require Import Free.Monad.

Class Strategy (Shape : Type) (Pos : Shape -> Type) :=
  {
    shareWith' : forall {A : Type},
      Free Shape Pos A      (* The computation to share. *)
        -> Free Shape Pos A (* The computation to share with deep sharing. *)
        -> Free Shape Pos (Free Shape Pos A);
    call : forall {A : Type},
      Free Shape Pos A -> Free Shape Pos (Free Shape Pos A);
  }.

(* Functions from [Strategy] lifted to [EvaluationStrategy]. *)
Definition shareWith (Shape : Type) (Pos : Shape -> Type)
                     (S : Strategy Shape Pos)
                     {A : Type}
                     (shareArgs : Strategy Shape Pos -> A -> Free Shape Pos A)
                     (fx : Free Shape Pos A)
 : Free Shape Pos (Free Shape Pos A)
  := @shareWith' Shape Pos S A fx (fx >>= shareArgs S).
