(** * Definition of a combination of two effects. *)

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


  (* Partial instances for the combination monad. *)
  Instance PartialL {F_Shape : Type} {F_Pos : F_Shape -> Type}
  {G_Shape : Type} {G_Pos : G_Shape -> Type} `(Partial F_Shape F_Pos) 
  : Partial (Shape F_Shape G_Shape) (Pos F_Pos G_Pos) := {
      undefined := fun {A : Type}                => Inl undefined;
      error     := fun {A : Type} (msg : string) => Inl (error msg)
    }.

  Instance PartialR {F_Shape : Type} {F_Pos : F_Shape -> Type}
  {G_Shape : Type} {G_Pos : G_Shape -> Type} `(Partial G_Shape G_Pos) 
  : Partial (Shape F_Shape G_Shape) (Pos F_Pos G_Pos) := {
      undefined := fun {A : Type}                => Inr undefined;
      error     := fun {A : Type} (msg : string) => Inr (error msg)
    }.

End Comb.

(* The type and smart constructor should be visible to other modules
   but to use the shape, position function or partial instance the
   identifier must be fully qualified, e.g. [Comb.PartialL]. *)
Export Comb.Monad.
