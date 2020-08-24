From Base Require Import Free.Monad.

Class ShareableArgs (Shape : Type) (Pos : Shape -> Type) 
                    (A : Type) :=
  {
    shareArgs : A -> Free Shape Pos A
  }.
(*
Instance ShareableArgsDummy (Shape : Type) (Pos : Shape -> Type)
                            (A : Type)
 : ShareableArgs Shape Pos A | 5 := {
    shareArgs := pure
 }.
*)