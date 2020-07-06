From Base Require Import Free.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Ltac simplifyInductionHypothesis ident1 ident2 :=
  match goal with
  | [ ident1 : ForFree ?Shape ?Pos ?A ?P (pure _) |- _ ] => inversion ident1 as [ Heq ident2 |]; clear ident1; subst Heq; simpl
  | [ ident1 : ForFree ?Shape ?Pos ?A ?P (impure ?s ?pf) |- _ ] =>
    dependent destruction ident1;
    match goal with
    | [ H1 : forall p : ?T, ForFree ?Shape ?Pos ?A ?P (?pf p), H0 : forall p, ForFree ?Shape ?Pos ?A ?Py (?pf p) -> _ = _,
        p : ?T |- _ ] =>
      specialize (H0 p (H1 p)) as ident2; clear H1; clear H0; simpl
    end
  end.

Tactic Notation "simplify'" ident(H) "as" ident(IH) := (simplifyInductionHypothesis H IH).

Ltac autoInductionHypothesis :=
  match goal with
  (*  | [ s : Zero__S |- _ ] => destruct s *)
  | [ H : ForFree ?Shape ?Pos ?A ?P (impure ?s ?pf) |- ?h ?s ?pf1 = ?h ?s ?pf2 ] =>
    f_equal; let x := fresh in
             extensionality x; simplify' H as Hnew; assumption
    (*   try apply newH) *)
  | [ H : ForFree ?Shape ?Pos ?A ?P (pure ?x) |- _ ] =>
    let newH := fresh in simplify' H as newH; rename newH into IH
  | [ H : forall p : ?T, ?f = ?g |- ?h ?s ?pf1 = ?h ?s ?pf2 ] =>
    f_equal; let x := fresh in extensionality x; apply H
  | [ H : forall p : ?T, ?f = ?g |- impure ?s ?pf1 = impure ?s ?pf2 ] =>
    f_equal; let x := fresh in extensionality x; apply H
  end.

Tactic Notation "autoIH" := (autoInductionHypothesis).

Tactic Notation "inductFree" ident(fx) "as" simple_intropattern(pat) := (induction fx as pat; simpl; try autoIH).
