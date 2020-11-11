From Base Require Import Free.Class.Strategy.
From Base Require Import Free.Monad.

Class ShareableArgs (Shape : Type) (Pos : Shape -> Type) (A : Type) :=
  { shareArgs : Strategy Shape Pos -> A -> Free Shape Pos A }.

(* ShareableArgs instance for functions.
   Effects inside of functions are not shared. *)
Instance ShareableArgsFunc (Shape : Type) (Pos : Shape -> Type) (A B : Type)
 : ShareableArgs Shape Pos (A -> B) :=
  { shareArgs _ := pure }.

(* Share operator with deep sharing. *)
Definition share (Shape : Type) (Pos : Shape -> Type)
                 (S : Strategy Shape Pos)
                 {A : Type} `{ShareableArgs Shape Pos A}
  : Free Shape Pos A -> Free Shape Pos (Free Shape Pos A)
 := shareWith Shape Pos S shareArgs.
