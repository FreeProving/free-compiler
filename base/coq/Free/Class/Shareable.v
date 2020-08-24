From Base Require Export Free.Instance.Share.

From Base Require Import Free.Monad.
From Base Require Import Free.Class.Injectable.
From Base Require Import Free.Class.ShareableArgs.

Class Shareable (Shape : Type) (Pos : Shape -> Type) 
                `{Injectable Share.Shape Share.Pos Shape Pos} :=
  {
    share : forall {A : Type} `{S : ShareableArgs Shape Pos A}, 
      Free Shape Pos A -> Free Shape Pos (Free Shape Pos A)
  }.