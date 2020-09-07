From Base Require Export Free.Instance.Share.
From Base Require Import Free.Class.Injectable.
From Base Require Import Free.Class.ShareableArgs.
From Base Require Import Free.Monad.

Class Strategy (Shape : Type) (Pos : Shape -> Type)
                `{Injectable Share.Shape Share.Pos Shape Pos} :=
  {
    share : forall {A : Type} `{ShareableArgs Shape Pos A},
      Free Shape Pos A -> Free Shape Pos (Free Shape Pos A);
    call : forall {A : Type},
      Free Shape Pos A -> Free Shape Pos (Free Shape Pos A);
  }.
