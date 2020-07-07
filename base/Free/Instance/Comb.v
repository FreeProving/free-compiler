(** * Definition of a combination of two effects. *)
From Base Require Import Free.Monad.

Module Comb.

  (* Shape and position function for the combination of effects. *)
  Definition Shape (F_Shape : Type) (G_Shape : Type) : Type := sum F_Shape G_Shape.
  Definition Pos {F_Shape : Type} {G_Shape : Type} 
    (F_Pos : F_Shape -> Type) (G_Pos : G_Shape -> Type) (s : Shape F_Shape G_Shape) : Type :=
    match s with
    | inl x => F_Pos x
    | inr x => G_Pos x
    end.

End Comb.