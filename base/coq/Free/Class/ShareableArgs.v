From Base Require Import Free.Monad.

Class ShareableArgs (Shape : Type) (Pos : Shape -> Type) 
                    (A : Type) :=
  {
    shareArgs : A -> Free Shape Pos A
  }.

(* ShareableArgs instance for functions. 
   Effects inside of functions are not shared. *)
Instance ShareableArgsFunc (Shape : Type) (Pos : Shape -> Type) (A B : Type)
 : ShareableArgs Shape Pos (A -> B) :=
  { shareArgs := pure }.