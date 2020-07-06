From Base Require Import Free Free.Instance.Maybe Free.Instance.Error Prelude Test.QuickCheck.
From Generated Require Import Proofs.Razor.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

(* Define some additional tactics. *)
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

(* Define induction scheme for [Expr]. *)
Section Expr_ind.

  Variable Shape : Type.
  Variable Pos   : Shape -> Type.
  Variable P     : Expr Shape Pos -> Prop.

  Hypothesis valP : forall (fn : Free Shape Pos (Integer.Integer Shape Pos)), P (val fn).

  Hypothesis addP : forall (fx fy : Free Shape Pos (Expr Shape Pos)),
    ForFree Shape Pos (Expr Shape Pos) P fx ->
      ForFree Shape Pos (Expr Shape Pos) P fy ->
        P (add0 fx fy).

  Fixpoint Expr_Ind (expr : Expr Shape Pos) : P expr.
  Proof.
    destruct expr as [ fn | fx fy ].
    - apply valP.
    - apply addP.
      + apply ForFree_forall. intros e IHe.
        inductFree fx as [ x | s pf IHpf ].
        * inversion IHe; subst. apply Expr_Ind.
        * dependent destruction IHe; subst. destruct H as [ p ].
          apply IHpf with (p := p). apply H.
      + apply ForFree_forall. intros e IHe.
        inductFree fy as [ y | s pf IHpf ].
        * inversion IHe; subst. apply Expr_Ind.
        * dependent destruction IHe; subst. destruct H as [ p ].
          apply IHpf with (p := p). apply H.
  Defined.

End Expr_ind.

(* The following lemma and theorem are proven in the file `AppendAssocProofs.v`. *)
Lemma append_nil : quickCheck prop_append_nil. Proof. Admitted.
Theorem append_assoc : quickCheck prop_append_assoc. Proof. Admitted.

Section Proofs_Maybe.

  (* In the following proofs we use the [Maybe] monad. *)
  Definition Shape   := Maybe.Shape.
  Definition Pos     := Maybe.Pos.
  Definition Partial := Maybe.Partial.

  (* In the [Maybe] monad exists only one impure value. *)
  Lemma impure_Nothing :
    forall (A : Type) (s : Shape) (pf : Pos s -> Free Shape Pos A),
      impure s pf = Nothing.
  Proof.
    intros A s pf.
    unfold Nothing. destruct s.
    f_equal.
    extensionality p. destruct p.
  Qed.

  (* If the stack is impure the result of any [exec] call on that stack will be impure. *)
  Lemma exec_strict_on_stack_arg :
    forall (fcode  : Free Shape Pos (Code Shape Pos)),
      exec Shape Pos Partial fcode Nothing = Nothing.
  Proof.
    intro fcode.
    destruct fcode as [ [ | [ [ fn | ] | sOp pfOp ] fcode1 ] | sCode pfCode ];
      simpl; apply impure_Nothing.
  Qed.

  (* The result of [exec] applied with the concatenation of some pieces of
     [Code] [fcode1] and [fcode2] to some stack, is the same as the result of
     [exec] applied with [fcode2] to the resulting stack of [exec] applied with
     [fcode2] to the same initial stack. *)
  Lemma exec_append :
    forall (fcode1 : Free Shape Pos (Code Shape Pos)),
    forall (fcode2 : Free Shape Pos (Code Shape Pos)),
    forall (fstack        : Free Shape Pos (Stack Shape Pos)),
        exec Shape Pos Partial (append Shape Pos fcode1 fcode2) fstack
        = exec Shape Pos Partial fcode2 (exec Shape Pos Partial fcode1 fstack).
  Proof.
    intros fcode1 fcode2.
    (* Destruct the monadic layer of the first piece of code. *)
    destruct fcode1 as [ code1 | sCode1 pfCode1 ].
    - (* fcode1 = pure code1 *)
      destruct code1 as [ | [ [ fn | ] | sOp pfOp ] fcode1' IHfcode1'] using List_Ind.
      + (* fcode1 = pure [] *)
        (* This case is trivial. *)
        intro fstack.
        destruct fstack as [ [ | fv fstack1 ] | sStack pfStack ]; try reflexivity.
        simpl. f_equal. do 2 rewrite impure_Nothing. reflexivity.
      + (* fcode1 = pure (pure (PUSH fn) : fcode1') *)
        intro fstack.
        (* Destruct the remaining code [fcode1'] to see, wether it is pure or impure. *)
        destruct fcode1' as [ code1' | sCode1' pfCode1' ].
        * (* fcode1 = pure (pure (PUSH fn) : pure code1') *)
          (* In this case we can apply the induction hypothesis. *)
          destruct fstack as [ [ | fv fstack1 ] | sStack pfStack ].
          { autoIH. apply IH. }
          { autoIH. apply IH. }
          { simpl. do 2 rewrite impure_Nothing. symmetry. apply exec_strict_on_stack_arg. }
        * (* fcode1 = pure (pure (PUSH fn) : impure sCode1' pfCode1' *)
          (* In this case we have impure code and therefore [H] can't hold. *)
          destruct fstack as [ [ | fv fstack1 ] | sStack pfStack ];
            simpl; do 2 rewrite impure_Nothing; symmetry; apply exec_strict_on_stack_arg.
      + (* fcode1 = pure (pure ADD : fcode1') *)
        intro fstack.
        (* Destruct the remaining code [fcode1'] to see, wether it is pure or impure. *)
        destruct fcode1' as [ code1' | sCode1' pfCode1' ].
        * (* fcode1 = pure (pure ADD : pure code1') *)
          (* As the addition reads its two inputs from the stack [fstack], we need to destruct it.
             All cases, where the stack does not contain at least two values, can't produce a pure result
             and are therefore a violation to [Hstack']. *)
          destruct fstack as [ [ | fv1 [ [ | fv2 fstack2 ] | sStack1 pfStack1 ] ] | sStack pfStack ];
            try (simpl; try do 2 rewrite impure_Nothing; symmetry; apply exec_strict_on_stack_arg).
          (* In the only valid case we can apply the induction hypothesis. *)
          autoIH. apply IH.
        * (* fcode1 = pure (pure ADD : impure sCode1' pfCode1') *)
          (* This case is again a violation to [Hstack'] which we can proof by destructing [fstack]. *)
          destruct fstack as [ [ | fv1 [ [ | fv2 fstack2 ] | sStack1 pfStack1 ] ] | sStack pfStack ];
            simpl; try do 2 rewrite impure_Nothing; symmetry; apply exec_strict_on_stack_arg.
      + (* fcode1 = pure (impure sOp pfOp : fcode1') *)
        (* In this case the first operation is impure, therefore we have another violation to [H]. *)
        intro fstack.
        destruct fstack as [ [ | fv1 [ [ | fv2 fstack2 ] | sStack1 pfStack1 ] ] | sStack pfStack ];
            simpl; try do 2 rewrite impure_Nothing; symmetry; apply exec_strict_on_stack_arg.
  - (* fcode1 = impure sCode1 pfCode1 *)
    (* In this case, where the whole [fcode1] is impure, we have another violation to [H]. *)
    intro fstack.
    simpl; try do 2 rewrite impure_Nothing; symmetry; apply exec_strict_on_stack_arg.
  Qed.

End Proofs_Maybe.
