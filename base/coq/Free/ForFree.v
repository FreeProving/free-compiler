From Base Require Import Free.Induction.
From Base Require Import Free.Monad.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Section SecForFree.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Inductive ForFree (A : Type) (P : A -> Prop) : Free Shape Pos A -> Prop :=
  | For_pure : forall (x : A), P x -> ForFree A P (pure x)
  | For_impure : forall (s : Shape) (pf : Pos s -> Free Shape Pos A),
      (forall p, ForFree A P (pf p)) -> ForFree A P (impure s pf).

  Lemma ForFree_bind :
    forall (A B : Type)
           (fx : Free Shape Pos A)
           (f : A -> Free Shape Pos B)
           (g : A -> Free Shape Pos B),
    ForFree A (fun x => f x = g x) fx -> fx >>= f = fx >>= g.
  Proof.
    intros.
    induction H; simpl.
    - apply H.
    - repeat apply f_equal.
      apply functional_extensionality; intros.
      apply H0.
  Qed.

  Inductive InFree (A : Type) : A -> Free Shape Pos A -> Prop :=
  | In_Pure : forall x, InFree A x (pure x)
  | In_Impure: forall x (s : Shape) (pf : Pos s -> Free Shape Pos A),
      (exists p, InFree A x (pf p)) -> InFree A x (impure s pf).

  Lemma ForFree_forall :
    forall (A : Type)
           (P : A -> Prop)
           (fx : Free Shape Pos A),
    ForFree A P fx <-> (forall (x : A), InFree A x fx -> P x).
  Proof.
    intros A P fx.
    intuition.
    - induction H.
      + inversion H0; subst; assumption.
      + dependent destruction H0. destruct H0.
        apply H1 with (p := x0). apply H0.
    - induction fx; simpl.
      + apply For_pure. apply H. apply In_Pure.
      + apply For_impure. intros p. apply H0. intros x HIn.
        apply H. apply In_Impure. exists p. apply HIn.
  Qed.

End SecForFree.
