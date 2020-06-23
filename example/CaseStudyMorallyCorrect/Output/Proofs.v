From Base Require Import Test.QuickCheck.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.
From Base Require Import Prelude.List.
From Generated Require Import FastLooseBasic.

Inductive List (A :Type) : Type :=
|nil : List A
|cons : A -> List A -> List A.

Arguments nil {_}.
Arguments cons {_} _ _.

Section rev.

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
rev ys xs = append (reverse xs) ys.
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


End rev.

Theorem rev_inv_rev: quickCheck (@prop_rev_is_rev_inv Identity.Shape Identity.Pos).
Proof.
  simpl.
  intros A totalList.
  induction totalList as [ xs | [] ] using Free_Ind.
  - induction xs as [ | x [xs' | []]] using List_Ind.
    + reflexivity.
    + simplify H as H'. simpl.
Qed.