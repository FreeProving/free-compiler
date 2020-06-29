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
Arguments rev_0 {_} {_} {_} _ _.
Arguments reverse {_} {_} {_} _ .
Arguments reverseNaive {_} {_} {_} _ .
Arguments reverseNaive_0 {_} {_} {_} _ .
Arguments append {_} {_} {_} _ _.
Arguments Nil {_} {_} {_}.
Arguments Cons {_} {_} {_} _ _.

Section reverseIsReverseNaive.

Lemma rev_0_rev: forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (xs : List Shape Pos A) (fys : Free Shape Pos (List Shape Pos A)),
  rev_0 xs fys = rev (pure xs) fys.
Proof.
  reflexivity.
Qed.

Lemma rev_acc_and_rest_list_connection': forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (xs : List Shape Pos A) (facc : Free Shape Pos (List Shape Pos A)),  
  rev (pure xs) facc = append (reverse (pure xs)) facc.
Proof.
  intros Shape Pos A xs.
  induction xs as [ | x fxs' ] using List_Ind; intros.
  - reflexivity.
  - induction fxs' as [ xs' | sh pos ] using Free_Ind.
    + simplify2 H as IHxs'. simpl. simpl in IHxs'. rewrite IHxs'. 
      rewrite IHxs' with (facc := Cons x Nil).
      rewrite <- append_assoc. reflexivity.
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
      rewrite rev_0_rev.
      rewrite rev_acc_and_rest_list_connection. rewrite IHxs'. reflexivity.
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

End reverseIsReverseNaive.

Section reverse_is_involution.

(*in appendProofs kopieren*)
  Lemma rewrite_Cons:
  forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fx : Free Shape Pos A) (fxs : Free Shape Pos (List Shape Pos A)),
    pure (cons fx fxs) = append (Cons fx Nil) fxs.
  Proof.
  reflexivity.
  Qed.  

Lemma reverseNaive_0_reverseNaive: forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (xs : List Shape Pos A),
  reverseNaive_0 xs = reverseNaive (pure xs).
Proof.
  reflexivity.
Qed.

Lemma reverseNaive_append : forall (A : Type)
  (fxs fys : Free Identity.Shape Identity.Pos (List Identity.Shape Identity.Pos A)),
      reverseNaive (append fxs fys) = append (reverseNaive fys) (reverseNaive fxs).
Proof.
intros A fxs.
destruct fxs as [ xs | [] _ ].
- induction xs as [| fx fxs' IHfxs'] using List_Ind; intros.
  + rewrite append_nil. simpl. reflexivity.
  + destruct fxs' as [ xs' | [] pf].
    * simplify2 IHfxs' as IHxs'. simpl reverseNaive at 3. rewrite reverseNaive_0_reverseNaive.
      rewrite append_assoc.
       rewrite <- IHxs'. reflexivity.
Qed.

Theorem reverseNaive_is_involution: forall (A : Type)
 (fxs : Free Identity.Shape Identity.Pos (List Identity.Shape Identity.Pos A)),
  reverseNaive (reverseNaive fxs) = fxs.
Proof.
  intros A fxs.
  destruct fxs as [ xs | [] _ ].
  - induction xs as [ | fx fxs' IHfxs' ] using List_Ind.
    + reflexivity.
    + destruct fxs' as [ xs' | [] pf].
      * simplify2 IHfxs' as IHxs'. simpl. rewrite reverseNaive_append.
        simpl in IHxs'. rewrite IHxs'. reflexivity.
Qed.

Theorem reverse_is_involution: quickCheck (@prop_rev_is_rev_inv Identity.Shape Identity.Pos).
Proof.
  simpl.
  intros A fxs.
  do 2 rewrite reverse_is_reverseNaive. 
  apply reverseNaive_is_involution.
Qed.

End reverse_is_involution.

Section minus_is_plus_inverse.

Theorem minus_is_plus_inv: quickCheck (@prop_minus_is_plus_inv Identity.Shape Identity.Pos).
Proof.
  simpl.
  intros fx fy.
  destruct fx as [ x | [] _ ].
  induction x as [ _ | 


End minus_is_plus_inverse.

