From Base Require Import Free.
From Base Require Import Prelude.List.
From Proofs Require Import Simplify.
From Proofs Require Import SimplLemmas.
From Generated Require Import FastLooseBasic.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Arguments append {_} {_} {_} _ _.
Arguments Nil {_} {_} {_}.
Arguments Cons {_} {_} {_} _ _.

Opaque Nil.
Opaque Cons.

Lemma rewrite_Cons: forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fx : Free Shape Pos A) (fxs : Free Shape Pos (List Shape Pos A)),
  Cons fx fxs = append (Cons fx Nil) fxs.
Proof.
  intros.
  rewrite apply_append_cons.
  rewrite apply_append_nil.
  reflexivity.
Qed. 

Lemma append_assoc' : forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (xs : List Shape Pos A) (fys fzs : Free Shape Pos (List Shape Pos A)),
  append (pure xs) (append fys fzs) = append (append (pure xs) fys) fzs.
Proof.
  intros.
  induction xs as [ | fx fxs IHimp ] using List_Ind.
  - reflexivity.
  - induction fxs as [ xs | s pf IHpf ] using Free_Ind; rewrite cons_Cons; do 3 rewrite apply_append_cons; f_equal. 
    + simplify H as IH'. apply IH'.
    + simpl. f_equal. extensionality x. simplify2 IHimp as IH. apply IH.
Qed.

Lemma append_assoc : forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fxs fys fzs : Free Shape Pos (List Shape Pos A)),
  append fxs (append fys fzs) = append (append fxs fys) fzs.
Proof.
  intros.
  induction fxs using Free_Ind.
  - apply append_assoc'.
  - simpl. f_equal. extensionality p.
    apply H.
Qed.

Lemma append_nil : forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fxs : Free Shape Pos (List Shape Pos A)),
  append fxs Nil = fxs.
Proof.
  intros Shape Pos A fxs.
  induction fxs as [ xs | s pf IHpf ] using Free_Ind.
  + induction xs as [ | fx fxs' IHfxs' ] using List_Ind.
    - reflexivity.
    - induction fxs' as [ xs' | s pf IHpf ] using Free_Ind; rewrite cons_Cons; rewrite apply_append_cons; f_equal.
      * simplify IHfxs' as IH. apply IH.
      * simpl. f_equal. extensionality x. simplify2 IHfxs' as IH. apply IH.
  + simpl. f_equal. extensionality x. apply IHpf.
Qed.




