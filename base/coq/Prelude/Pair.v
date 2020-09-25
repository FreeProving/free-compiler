From Base Require Import Free.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Malias.

Require Import Coq.Program.Equality.

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

  Variable A B C D : Type.

  Definition nf'Pair `{Normalform Shape Pos A C}
                     `{Normalform Shape Pos B D}
                     (p : Pair Shape Pos A B)
    : Free Shape Pos (Pair Identity.Shape Identity.Pos C D)
   := match p with
       | pair_ fa fb => nf fa >>= fun na =>
                        nf fb >>= fun nb =>
                        pure (pair_ (pure na) (pure nb))
       end.

  Global Instance NormalformPair `{Normalform Shape Pos A C}
                                 `{Normalform Shape Pos B D}
    : Normalform Shape Pos (Pair Shape Pos A B)
                           (Pair Identity.Shape Identity.Pos C D)
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

(* ForPair *)
Inductive ForPair (Shape : Type) (Pos : Shape -> Type) (a b : Type) (P0
    : a -> Prop) (P1 : b -> Prop)
   : Pair Shape Pos a b -> Prop
  := ForPair_pair_
   : forall (x : Free Shape Pos a) (x0 : Free Shape Pos b),
     ForFree Shape Pos a P0 x ->
     ForFree Shape Pos b P1 x0 ->
     ForPair Shape Pos a b P0 P1 (@pair_ Shape Pos a b x x0).

Inductive InPair_1 (Shape : Type) (Pos : Shape -> Type) (a b : Type)
   : a -> Pair Shape Pos a b -> Prop
  := InPair_1_pair_
   : forall (x1 : a) (x : Free Shape Pos a) (x0 : Free Shape Pos b),
     InFree Shape Pos a x1 x ->
     InPair_1 Shape Pos a b x1 (@pair_ Shape Pos a b x x0)
with InPair_2 (Shape : Type) (Pos : Shape -> Type) (a b : Type)
   : b -> Pair Shape Pos a b -> Prop
  := InPair_2_pair_
   : forall (x1 : b) (x : Free Shape Pos a) (x0 : Free Shape Pos b),
     InFree Shape Pos b x1 x0 ->
     InPair_2 Shape Pos a b x1 (@pair_ Shape Pos a b x x0).

Lemma ForPair_forall : forall (Shape : Type)
  (Pos : Shape -> Type)
  (a b : Type)
  (P0 : a -> Prop)
  (P1 : b -> Prop)
  (x : Pair Shape Pos a b),
  ForPair Shape Pos a b P0 P1 x <->
  ((forall (y : a), InPair_1 Shape Pos a b y x -> P0 y) /\
   (forall (y : b), InPair_2 Shape Pos a b y x -> P1 y)).
Proof.
  intros Shape Pos a b.
  prove_forall Pair_ind.
Qed.

(* Add hints for proof generation *)
Hint Extern 0 (ForPair _ _ _ _ _ _ ?x) =>
  prove_ind_prove_ForType x ForPair_forall pair_induction : prove_ind_db.
