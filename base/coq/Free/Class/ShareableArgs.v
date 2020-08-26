From Base Require Import Free.Monad.

Class ShareableArgs (Shape : Type) (Pos : Shape -> Type) 
                    (A : Type) :=
  {
    shareArgs : A -> Free Shape Pos A
  }.