From Base Require Import Free Free.Instance.Maybe Prelude.
From Extra Require Import ExprInd Tactic.
From Generated Require Import Razor.
From Proofs Require Import AppendAssocProofs.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

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
          (* In this case we can apply the induction hypothesis if we have a pure stack.
             Otherwise the result is undefined on both sides. *)
          destruct fstack as [ [ | fv fstack1 ] | sStack pfStack ].
          { autoIH. apply IH. }
          { autoIH. apply IH. }
          { simpl. do 2 rewrite impure_Nothing. symmetry. apply exec_strict_on_stack_arg. }
        * (* fcode1 = pure (pure (PUSH fn) : impure sCode1' pfCode1' *)
          (* In this case the result is undefined on both sides. *)
          destruct fstack as [ [ | fv fstack1 ] | sStack pfStack ];
            simpl; do 2 rewrite impure_Nothing; symmetry; apply exec_strict_on_stack_arg.
      + (* fcode1 = pure (pure ADD : fcode1') *)
        intro fstack.
        (* Destruct the remaining code [fcode1'] to see, wether it is pure or impure. *)
        destruct fcode1' as [ code1' | sCode1' pfCode1' ].
        * (* fcode1 = pure (pure ADD : pure code1') *)
          (* As the addition reads its two inputs from the stack [fstack], we need to destruct it.
             All cases, where the stack does not contain at least two values, produce an undefined. *)
          destruct fstack as [ [ | fv1 [ [ | fv2 fstack2 ] | sStack1 pfStack1 ] ] | sStack pfStack ];
            try (simpl; try do 2 rewrite impure_Nothing; symmetry; apply exec_strict_on_stack_arg).
          (* In the only valid case we can apply the induction hypothesis. *)
          autoIH. apply IH.
        * (* fcode1 = pure (pure ADD : impure sCode1' pfCode1') *)
          (* In this case the result is undefined on both sides. *)
          destruct fstack as [ [ | fv1 [ [ | fv2 fstack2 ] | sStack1 pfStack1 ] ] | sStack pfStack ];
            simpl; try do 2 rewrite impure_Nothing; symmetry; apply exec_strict_on_stack_arg.
      + (* fcode1 = pure (impure sOp pfOp : fcode1') *)
        (* In this case the result is undefined on both sides. *)
        intro fstack.
        destruct fstack as [ [ | fv1 [ [ | fv2 fstack2 ] | sStack1 pfStack1 ] ] | sStack pfStack ];
            simpl; try do 2 rewrite impure_Nothing; symmetry; apply exec_strict_on_stack_arg.
  - (* fcode1 = impure sCode1 pfCode1 *)
    (* In this case the result is undefined on both sides. *)
    intro fstack.
    simpl; try do 2 rewrite impure_Nothing; symmetry; apply exec_strict_on_stack_arg.
  Qed.

End Proofs_Maybe.
