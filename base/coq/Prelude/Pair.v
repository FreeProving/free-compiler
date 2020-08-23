From Base Require Import Free.

Section SecPair.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).

  Inductive Pair (A B : Type) : Type :=
    | pair_ : Free' A -> Free' B -> Pair A B.

End SecPair.

(* smart constructor *)

Notation "'Pair_' Shape Pos x y" :=
  (@pure Shape Pos (Pair Shape Pos _ _) (@pair_ Shape Pos _ _ x y))
  ( at level 10, Shape, Pos, x, y at level 9 ).

Notation "'@Pair_' Shape Pos A B x y" :=
  (@pure Shape Pos (Pair Shape Pos A B) (@pair_ Shape Pos A B x y))
  ( only parsing, at level 10, Shape, Pos, A, B, x, y at level 9 ).
 
Arguments pair_  {Shape} {Pos} {A} {B}.
