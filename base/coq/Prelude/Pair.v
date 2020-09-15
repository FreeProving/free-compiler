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

(* ForPair_A *)
Inductive ForPair_A (Shape : Type) (Pos : Shape -> Type) (A B : Type) (P : A -> Prop)
    : Pair Shape Pos A B -> Prop :=
  | ForPair_A_pair : forall (fx : Free Shape Pos A)
                      (fy : Free Shape Pos B),
      ForFree Shape Pos A P fx ->
      ForPair_A Shape Pos A B P (@pair_ Shape Pos A B fx fy).

Inductive InPair_A (Shape : Type) (Pos : Shape -> Type) (A B : Type)
    : A -> Pair Shape Pos A B -> Prop :=
  | InPair_A_pair_fx : forall (x  : A)
                          (fx : Free Shape Pos A)
                          (fy : Free Shape Pos B),
      InFree Shape Pos A x fx ->
      InPair_A Shape Pos A B x (@pair_ Shape Pos A B fx fy).

Lemma ForPair_A_forall (Shape : Type) (Pos : Shape -> Type) (A B : Type)
  : forall (P : A -> Prop)
           (fp : Pair Shape Pos A B),
    ForPair_A Shape Pos A B P fp <-> (forall (x : A), InPair_A Shape Pos A B x fp -> P x).
Proof.
  Hint Extern 0 (ForPair_A ?Shape ?Pos ?A ?B _ _) => forall_finish2 (@InPair_A_pair_fx Shape Pos A B) : prove_forall_db2.
  prove_forall Pair_ind.
Qed.

(* ForPair_B *)
Inductive ForPair_B (Shape : Type) (Pos : Shape -> Type) (A B : Type) (P : B -> Prop)
    : Pair Shape Pos A B -> Prop :=
  | ForPair_B_pair : forall (fx : Free Shape Pos A)
                      (fy : Free Shape Pos B),
      ForFree Shape Pos B P fy ->
      ForPair_B Shape Pos A B P (@pair_ Shape Pos A B fx fy).

Inductive InPair_B (Shape : Type) (Pos : Shape -> Type) (A B : Type)
    : B -> Pair Shape Pos A B -> Prop :=
  | InPair_B_pair_fy : forall (y  : B)
                          (fx : Free Shape Pos A)
                          (fy : Free Shape Pos B),
      InFree Shape Pos B y fy ->
      InPair_B Shape Pos A B y (@pair_ Shape Pos A B fx fy).

Lemma ForPair_B_forall (Shape : Type) (Pos : Shape -> Type) (A B : Type)
  : forall (P : B -> Prop)
           (fp : Pair Shape Pos A B),
    ForPair_B Shape Pos A B P fp <-> (forall (x : B), InPair_B Shape Pos A B x fp -> P x).
Proof.
  Hint Extern 0 (ForPair_B ?Shape ?Pos ?A ?B _ _) => forall_finish2 (@InPair_B_pair_fy Shape Pos A B) : prove_forall_db2.
  prove_forall Pair_ind.
Qed.

(* Add hints for proof generation *)
Local Ltac pair_induction x := induction x as [ fx fy ] using Pair_ind.
Hint Extern 0 (ForPair_A ?Shape ?Pos ?A ?B _ _) => prove_ind_prove_for_type
    (Pair Shape Pos A B)
    (ForPair_A Shape Pos A B)
    (ForPair_A_forall Shape Pos A B)
    (pair_induction)
  : prove_ind_db.
Hint Extern 0 (ForPair_B ?Shape ?Pos ?A ?B _ _) => prove_ind_prove_for_type
    (Pair Shape Pos A B)
    (ForPair_B Shape Pos A B)
    (ForPair_B_forall Shape Pos A B)
    (pair_induction)
  : prove_ind_db.
Local Ltac forall_ForPair_A_InPair_A :=
  match goal with
    | [ HF : ForPair_A ?Shape ?Pos ?A ?B _ ?fx
      , HI : InPair_A ?Shape ?Pos ?A ?B ?x ?fx
    |- _ ] =>
      rewrite ForPair_A_forall in HF;
      specialize (HF x HI)
  end.
Hint Extern 0 => forall_ForPair_A_InPair_A : prove_forall_db.
Local Ltac forall_ForPair_B_InPair_B :=
  match goal with
    | [ HF : ForPair_B ?Shape ?Pos ?A ?B _ ?fx
      , HI : InPair_B ?Shape ?Pos ?A ?B ?x ?fx
    |- _ ] =>
      rewrite ForPair_B_forall in HF;
      specialize (HF x HI)
  end.
Hint Extern 0 => forall_ForPair_B_InPair_B : prove_forall_db.
Local Ltac forall_ForPair_A :=
  match goal with
  | [ HF : ForPair_A ?Shape ?Pos ?T1 ?T2 _ ?fx
    |- ForPair_A ?Shape ?Pos ?T1 ?T2 _ ?fx ] =>
       let x  := fresh "x"
    in let HI := fresh "HI"
    in apply ForPair_A_forall; intros x HI;
       rewrite ForPair_A_forall in HF;
       specialize (HF x HI)
  | [ H : forall y : ?A, _ |- ForPair_A ?Shape ?Pos ?T1 ?T2 ?P ?fx ] =>
       let x  := fresh "x"
    in let HI := fresh "HI"
    in apply ForPair_A_forall; intros x HI;
       specialize (H x)
  end.
Hint Extern 0 => forall_ForPair_A : prove_forall_db2.
Local Ltac forall_ForPair_B :=
  match goal with
  | [ HF : ForPair_B ?Shape ?Pos ?T1 ?T2 _ ?fx
    |- ForPair_B ?Shape ?Pos ?T1 ?T2 _ ?fx ] =>
       let x  := fresh "x"
    in let HI := fresh "HI"
    in apply ForPair_B_forall; intros x HI;
       rewrite ForPair_B_forall in HF;
       specialize (HF x HI)
  | [ H : forall y : ?A, _ |- ForPair_B ?Shape ?Pos ?T1 ?T2 ?P ?fx ] =>
       let x  := fresh "x"
    in let HI := fresh "HI"
    in apply ForPair_B_forall; intros x HI;
       specialize (H x)
  end.
Hint Extern 0 => forall_ForPair_B : prove_forall_db2.
