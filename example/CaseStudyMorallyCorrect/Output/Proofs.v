From Base Require Import Test.QuickCheck.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.
From Base Require Import Prelude.List.
From Generated Require Import FastLooseBasic.
From Generated Require Import AppendProofs.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Arguments rev {_} {_} {_} _ _.
Arguments reverse {_} {_} {_} _ .
Arguments reverseNaive {_} {_} {_} _ .
Arguments append {_} {_} {_} _ _.


(*Section rev.

Variable A : Type.

Fixpoint rev (acc : List A) (xs : List A) : List A :=
  match xs with
  | nil => acc
  | cons x xs' => rev (cons x acc) xs'
  end.

Definition reverse (xs : List A) : List A :=
 rev nil xs.

Fixpoint append (xs : List A) (ys : List A) : List A :=
match xs with
| nil => ys
| cons x xs' => cons x (append xs' ys)
end.

Fixpoint reverse2 (xs : List A) : List A :=
match xs with
| nil => nil
| cons x xs => append (reverse2 xs) (cons x nil)
end.


Theorem app_nil: forall (xs : List A), append xs nil = xs.
Proof.
Admitted.

Theorem rev_append: forall (xs : List A) (ys : List A),
rev xs acc = append (reverse xs) ys.
Proof.
intros xs.
induction xs.
- reflexivity.
- simpl.
  intros. unfold reverse. simpl. rewrite IHxs. rewrite IHxs.
Admitted.


Theorem reverse2_reverse1: forall (xs : List A), reverse2 xs = reverse xs.
Proof.
intros.
induction xs.
- reflexivity.
- simpl. unfold reverse. simpl. rewrite rev_append. rewrite IHxs. reflexivity.
Qed.


End rev.*)

Section reverseIsReverseNaive.

Lemma rev_acc_and_rest_list_connection': forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (xs : List Shape Pos A) (facc : Free Shape Pos (List Shape Pos A)),  
  rev (pure xs) facc = append (reverse (pure xs)) facc.
Proof.
  intros Shape Pos A xs.
  induction xs as [ | x fxs' ] using List_Ind; intros.
  - reflexivity.
  - induction fxs' as [ xs' | sh pos ] using Free_Ind.
    + simplify H as IHxs'. simpl. simpl in IHxs'. rewrite IHxs'. rewrite IHxs'. 
      assert (H : rev_0 Shape Pos xs' (Cons Shape Pos x (Nil Shape Pos)) = 
           append (rev_0 Shape Pos xs' (Nil Shape Pos)) (Cons Shape Pos x (Nil Shape Pos))).
      {rewrite IHxs'. reflexivity. }
      rewrite H. rewrite append_nil. rewrite <- append_assoc. reflexivity.
    + 

Lemma rev_acc_and_rest_list_connection: forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fxs : Free Shape Pos (List Shape Pos A)) (facc : Free Shape Pos (List Shape Pos A)),
  rev fxs facc = append (reverse fxs) facc.
Proof.
  intros Shape Pos A fxs facc.
  induction fxs as [ xs | sh pos ] using Free_Ind.
  - 


Lemma reverse_is_reverseNaive': forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (xs : List Shape Pos A),
  reverse Shape Pos (pure xs) = reverseNaive Shape Pos (pure xs).
Proof.
  intros Shape Pos A xs.
  induction xs as [ | x fxs' ] using List_Ind.
  - reflexivity.
  - induction fxs' as [ xs' | sh pos ] using Free_Ind.
    + simplify H as IHxs'. unfold reverse. 


Theorem reverse_is_reverseNaive: quickCheck prop_reverse_is_reverseNaive.
Proof.
  simpl.
  intros Shape Pos A fxs.
  induction fxs as [ xs | sh pos ] using Free_Ind.
  - 

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