(* A class representing the membership relation between an effect and an effect stack *)

From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Monad.
From Base Require Import Free.Class.Partial.

(* injS embeds an effect in an effect stack that contains it.
   injP allows us to view a position of an embedded effect as an
   element of the effect itself. *)
Class Injectable (SubShape : Type) (SubPos : SubShape -> Type)
  (SupShape : Type) (SupPos : SupShape -> Type) :=
  {
    injS : SubShape -> SupShape;
    injP : forall {s : SubShape}, SupPos (injS s) -> SubPos s;
 }.

(* Injectable instances *)

(* Every effect is contained in itself. *)
Instance Inject_refl {Shape : Type} {Pos : Shape -> Type}
 : Injectable Shape Pos Shape Pos | 0 := {
      injS := fun s => s;
      injP s := fun p => p;
  }.

(* An effect is contained in an effect stack if it is its head component. *)
Instance Inject_comb {F_Shape : Type} {F_Pos : F_Shape -> Type}
   {G_Shape : Type} {G_Pos : G_Shape -> Type}
   : Injectable F_Shape F_Pos (Comb.Shape F_Shape G_Shape)
   (Comb.Pos F_Pos G_Pos) | 1 := {
      injS := inl;
      injP s := fun p : F_Pos s => p;
   }.

(* An effect is also contained in an effect stack if it is contained in its tail. *)
Instance Inject_rec {F_Shape : Type} {F_Pos : F_Shape -> Type}
   {G_Shape : Type} {G_Pos : G_Shape -> Type}
   {H_Shape : Type} {H_Pos : H_Shape -> Type}
   `{Injectable F_Shape F_Pos H_Shape H_Pos}
   : Injectable F_Shape F_Pos
   (Comb.Shape G_Shape H_Shape) (Comb.Pos G_Pos H_Pos) | 2 := {
      injS := fun s => inr (injS s);
      injP s := fun p => injP p;
   }.
