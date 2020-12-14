From Base Require Import Free.
From Base Require Import Free.Instance.ND.

Notation "'NonDet' Shape Pos" := (Injectable ND.Shape ND.Pos Shape Pos)
  ( at level 10, Shape, Pos at level 9 ).

Definition choice (Shape : Type) (Pos : Shape -> Type) (ND : NonDet Shape Pos)
                  {A : Type} (x : Free Shape Pos A) (y : Free Shape Pos A)
  : Free Shape Pos A
 := @Choice Shape Pos A ND x y.

Definition failed (Shape : Type) (Pos : Shape -> Type) (ND : NonDet Shape Pos)
                {A : Type}
  : Free Shape Pos A
 := @Fail Shape Pos ND A.
