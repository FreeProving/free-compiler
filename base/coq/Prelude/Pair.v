From Base Require Import Free.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Malias.

From Base Require Import Prelude.Bool.

Section SecPair.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).

  Inductive Pair (A B : Type) : Type :=
    | pair_ : Free' A -> Free' B -> Pair A B.

  Arguments pair_ {A} {B}.

End SecPair.

Notation "'Pair_' Shape Pos x y" :=
  (@pure Shape Pos (Pair Shape Pos _ _) (@pair_ Shape Pos _ _ x y))
  ( at level 10, Shape, Pos, x, y at level 9 ).

Notation "'@Pair_' Shape Pos A B x y" :=
  (@pure Shape Pos (Pair Shape Pos A B) (@pair_ Shape Pos A B x y))
  ( only parsing, at level 10, Shape, Pos, A, B, x, y at level 9 ).

Arguments pair_  {Shape} {Pos} {A} {B}.

(* Normalform instance for Pair *)
Section SecNFPair.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Variable A B : Type.

  Definition nf'Pair `{Normalform Shape Pos A}
                     `{Normalform Shape Pos B}
                     (p : Pair Shape Pos A B)
    : Free Shape Pos (Pair Identity.Shape Identity.Pos 
                     (@nType Shape Pos A _) (@nType Shape Pos B _))
   := match p with
       | pair_ fa fb => nf fa >>= fun na =>
                        nf fb >>= fun nb =>
                        pure (pair_ (pure na) (pure nb))
       end.

  Global Instance NormalformPair `{Normalform Shape Pos A}
                                 `{Normalform Shape Pos B}
    : Normalform Shape Pos (Pair Shape Pos A B)
   := { nf' := nf'Pair }.

End SecNFPair.

(* ShareableArgs instance for Pair *)
Instance ShareableArgsPair {Shape : Type} {Pos : Shape -> Type} (A B : Type)
                        `{Injectable Share.Shape Share.Pos Shape Pos}
                        `{SAA : ShareableArgs Shape Pos A}
                        `{SAB : ShareableArgs Shape Pos B}
  : ShareableArgs Shape Pos (Pair Shape Pos A B) := {
     shareArgs p := match p with
                    | pair_ fx fy => cbneed Shape Pos (@shareArgs Shape Pos A SAA) fx >>= fun sx =>
                                     cbneed Shape Pos (@shareArgs Shape Pos B SAB) fy >>= fun sy =>
                                     (pure (pair_ sx sy))
                    end
   }.
