(** * Definition of a combination of two effect functors. *)

From Base Require Import Free.

Module Comb.

  (* Shape and position function for the combination of effects. *)
  Definition Shape (F_Shape : Type) (G_Shape : Type) : Type := sum F_Shape G_Shape.
  Definition Pos {F_Shape : Type} {G_Shape : Type} 
    (F_Pos : F_Shape -> Type) (G_Pos : G_Shape -> Type) (s : Shape F_Shape G_Shape) : Type :=
    match s with
    | inl x => F_Pos x
    | inr x => G_Pos x
    end.

  (* Type synonym and smart constructors for the combination of effects. *)
  Module Import Monad.
    Definition Comb (F_Shape : Type) (F_Pos : F_Shape -> Type) 
    (G_Shape : Type) (G_Pos : G_Shape -> Type) (A : Type) : Type := 
         Free (Shape F_Shape G_Shape) (Pos F_Pos G_Pos) A.

    Fixpoint Inl {A : Type} {F_Shape : Type} {F_Pos : F_Shape -> Type} 
    {G_Shape : Type} {G_Pos : G_Shape -> Type} 
    (ffx : Free F_Shape F_Pos A) : Comb F_Shape F_Pos G_Shape G_Pos A := 
        match ffx with
        | pure x => pure x
        | impure s pf => impure ((inl s) : Shape F_Shape G_Shape) 
          (fun p => Inl (pf p))
        end.
    Fixpoint Inr {A : Type} {F_Shape : Type} {F_Pos : F_Shape -> Type} 
    {G_Shape : Type} {G_Pos : G_Shape -> Type} 
    (fgx : Free G_Shape G_Pos A) : Comb F_Shape F_Pos G_Shape G_Pos A := 
        match fgx with
        | pure x => pure x
        | impure s pf => impure ((inr s) : Shape F_Shape G_Shape) 
          (fun p => Inr (pf p))
        end.

  End Monad.

End Comb.

(* The type and smart constructor should be visible to other modules
   but to use the shape, position function or partial instance the
   identifier must be fully qualified, i.e. [Comb.Monad]. *)
Export Comb.Monad.
