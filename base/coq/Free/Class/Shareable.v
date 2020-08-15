From Base Require Import Free.Monad.
From Base Require Import Free.Class.ShareableArgs.

(*
Class Shareable (Shape : Type) (Pos : Shape -> Type) 
                (P : Type -> Prop):=
  {
    share (A : Type) 
     : P A -> Free Shape Pos A -> Free Shape Pos (Free Shape Pos A)
  }.
*)

Class Shareable (Shape : Type) (Pos : Shape -> Type) :=
  {
    share : forall {A : Type} `{S : ShareableArgs Shape Pos A}, Free Shape Pos A -> Free Shape Pos (Free Shape Pos A)
  }.
(*Arguments share Shape Pos Shareable {A} {S} p.*)

(*
Class Shareable (Shape : Type) (Pos : Shape -> Type) :=
  {
    share : forall {A : Type}, Free Shape Pos A -> Free Shape Pos (Free Shape Pos A)
  }.
*)