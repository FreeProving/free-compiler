From Base Require Import Free.
From Base Require Import Prelude.List.
From Generated Require Import FastLooseBasic.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Arguments append {_} {_} {_} _ _.

Lemma append_assoc' : forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (xs : List Shape Pos A) (fys fzs : Free Shape Pos (List Shape Pos A)),
  append (pure xs) (append fys fzs) = append (append (pure xs) fys) fzs.
Proof.
  intros.
  induction xs as [| fx fxs IH] using List_Ind.
  - reflexivity.
  - induction fxs as [xs | s pf IHpf] using Free_Ind.
    + simpl. f_equal. simplify H as IH'. simpl in IH'. apply IH'.
    + simpl. do 2 apply f_equal. extensionality x.
Admitted. 

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
  append fxs (Nil Shape Pos) = fxs.
Proof.
Admitted.




