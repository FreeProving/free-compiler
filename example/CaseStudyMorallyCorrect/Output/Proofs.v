From Base Require Import Test.QuickCheck.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.
From Base Require Import Prelude.List.
From Generated Require Import FastLooseBasic.
From Generated Require Import AppendProofs.
From Generated Require Import Simplify.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Arguments rev {_} {_} {_} _ _.
Arguments reverse {_} {_} {_} _ .
Arguments reverseNaive {_} {_} {_} _ .
Arguments append {_} {_} {_} _ _.

Section reverseIsReverseNaive.

Lemma rev_acc_and_rest_list_connection': forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (xs : List Shape Pos A) (facc : Free Shape Pos (List Shape Pos A)),  
  rev (pure xs) facc = append (reverse (pure xs)) facc.
Proof.
  intros Shape Pos A xs.
  induction xs as [ | x fxs' ] using List_Ind; intros.
  - reflexivity.
  - induction fxs' as [ xs' | sh pos ] using Free_Ind.
    + simplify2 H as IHxs'. simpl. simpl in IHxs'. rewrite IHxs'. rewrite IHxs'. 
      assert (H : rev_0 Shape Pos xs' (Cons Shape Pos x (Nil Shape Pos)) = 
           append (rev_0 Shape Pos xs' (Nil Shape Pos)) (Cons Shape Pos x (Nil Shape Pos))).
      {rewrite IHxs'. reflexivity. }
      rewrite H. rewrite append_nil. rewrite <- append_assoc. reflexivity.
    + simpl. f_equal. extensionality x0. simplify2 H0 as H0'. apply H0'.
Qed.

Lemma rev_acc_and_rest_list_connection: forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fxs : Free Shape Pos (List Shape Pos A)) (facc : Free Shape Pos (List Shape Pos A)),
  rev fxs facc = append (reverse fxs) facc.
Proof.
  intros Shape Pos A fxs facc.
  induction fxs as [ xs | sh pos ] using Free_Ind.
  - apply rev_acc_and_rest_list_connection'.
  - simpl. f_equal. extensionality x. apply H.
Qed.

Lemma reverse_is_reverseNaive': forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (xs : List Shape Pos A),
  reverse (pure xs) = reverseNaive (pure xs).
Proof.
  intros Shape Pos A xs.
  induction xs as [ | x fxs' ] using List_Ind.
  - reflexivity.
  - induction fxs' as [ xs' | sh pos ] using Free_Ind.
    + simplify H as IHxs'. simpl reverseNaive. simpl reverse.
      assert  (H : rev_0 Shape Pos xs' (Cons Shape Pos x (Nil Shape Pos)) = 
                   rev (pure xs') (Cons Shape Pos x (Nil Shape Pos))).
      {reflexivity. }
      rewrite H. rewrite rev_acc_and_rest_list_connection. rewrite IHxs'. reflexivity.
    + simpl. f_equal. extensionality x0. simplify2 H0 as H0'. apply H0'.
Qed.


Theorem reverse_is_reverseNaive: quickCheck prop_reverse_is_reverseNaive.
Proof.
  simpl.
  intros Shape Pos A fxs.
  induction fxs as [ xs | sh pos ] using Free_Ind.
  - apply reverse_is_reverseNaive'.
  - simpl. f_equal. extensionality x. apply H.
Qed.

Theorem rev_inv_rev: quickCheck (@prop_rev_is_rev_inv Identity.Shape Identity.Pos).
Proof.
  simpl.
  intros A totalList.
  induction totalList as [ xs | [] ] using Free_Ind.
  - induction xs as [ | x [xs' | []]] using List_Ind.
    + reflexivity.
    + simplify H as H'. simpl.

Qed.

Section reverseIsReverseNaive.