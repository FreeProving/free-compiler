From Base Require Import Free.
Require Import Coq.Program.Equality.

Ltac typeof s := let T := type of s in T.

Ltac checkHypothesisIdent ident :=
  first [ rename ident into HypTmp; rename HypTmp into ident
        | fail 1 "No such hypothesis" ident ].

Ltac checkFreshIdent ident :=
  first [ rename ident into HypTmp; rename HypTmp into ident;
          fail 1 ident "is already used"
         | idtac ].

Ltac simplifyInductionHypothesis2 ident1 ident2 :=
  match goal with
  | [ H0 : ForFree ?Shape ?Pos ?A ?P (impure ?s ?pf) |- _ ] =>
    dependent destruction H0; try (rename ident2 into Htmp);
    match goal with
    | [ H1 : forall p, ForFree ?Shape ?Pos ?A _ (?pf p)
      , H0 : forall p, ForFree ?Shape ?Pos ?A _ (?pf p) -> _ = _
      , p : ?Pos ?s |- _ ] =>
      first [ injection (H0 p (H1 p)) as ident2
            | specialize (H0 p (H1 p)) as ident2];
      clear H1; clear H0;
      try (rename Htmp into ident2)
    end
  end.

Ltac searchForInducionHypothesis ident1 ident2 :=
  checkHypothesisIdent ident1;
  checkFreshIdent ident2;
  match typeof ident1 with
  | context [?s] =>
    match s with
    | ForFree ?Shape ?Pos ?A ?P (pure _) =>
      inversion ident1 as [ Heq ident2 |]; clear ident1; subst
    | ForFree ?Shape ?Pos ?A ?P (impure ?s ?pf) =>
      simplifyInductionHypothesis2 ident1 ident2
    | forall (p : ?Pos ?s), ForFree ?Shape ?Pos ?A ?P (?pf p) -> _ = _ =>
      simplifyInductionHypothesis2 ident1 ident2
    | _ => fail 1 "The tactic cannot be applied to the hypothesis" ident1
    end
  end.

Tactic Notation "simplify2" ident(H) "as" ident(IH) :=
  (searchForInducionHypothesis H IH).
