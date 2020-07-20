(* This file is a variant of [RazorProofsMaybe] but it is using the advanced
   tactics of [Extra/FreeDB]. *)

From Base Require Import Free Free.Instance.Maybe Prelude QuickCheck.
From Razor.Extra Require Import ExprInd FreeDB Pureness Tactic.
From Generated Require Import Razor.
From Proofs Require Import AppendAssocProofs.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Section Proofs.

  Definition Shape := Maybe.Shape.
  Definition Pos := Maybe.Pos.
  Definition Part := Maybe.Partial.

  (* If the stack is [Nothing] the result of any [exec] call on that stack will also be [Nothing]. *)
  Lemma exec_strict_on_stack_arg :
    forall (fcode  : Free Shape Pos (Code Shape Pos)),
      exec Part fcode Nothing = Nothing.
  Proof with (autodef).
    intro fcode.
    destruct fcode as [ [ | [ [ fn | ] | sOp pfOp ] fcode1 ] | sCode pfCode ]...
  Qed.

  (* The result of [exec] applied with the concatenation of some pieces of
     [Code] [fcode1] and [fcode2] to some stack, is the same as the result of
     [exec] applied with [fcode2] to the resulting stack of [exec] applied with
     [fcode2] to the same initial stack. *)
  Lemma exec_append :
    forall (fcode1 : Free Shape Pos (Code Shape Pos)),
    forall (fcode2 : Free Shape Pos (Code Shape Pos)),
    forall (fstack        : Free Shape Pos (Stack Shape Pos)),
        exec Part (append fcode1 fcode2) fstack
        = exec Part fcode2 (exec Part fcode1 fstack).
  Proof with (pretty; try reflexivity ).
    intros fcode1 fcode2.
    (* Destruct the monadic layer of the first piece of code. *)
    destruct fcode1 as [ code1 | ]...
    - (* fcode1 = pure code1 *)
      induction code1 as [ | [ [ fn | ] | ] fcode1' IHfcode1'] using List_Ind...
      + (* fcode1 = Nil *)
        (* This case is trivial. *)
        intro fstack.
        rewrite def_append_Nil...
        destruct fstack as [ stack | ]; autodef.
      + (* fcode1 = Cons (PUSH fn) fcode1' *)
        intro fstack.
        setoid_rewrite def_append_Cons...
        destruct fstack as [ stack | ]...
        * (* If the stack is pure we can apply the definition of [exec]. *)
          setoid_rewrite def_exec_PUSH...
          (* Finish proof with induction. *)
          destruct fcode1' as [ code1' | ]...
          { autoIH; apply IH. }
          { autodef.
            rewrite exec_strict_on_stack_arg... }
        * (* If the stack is [Nothing], the result is [Nothing] as well. *)
          autodef.
          rewrite exec_strict_on_stack_arg...
      + (* fcode1 = Cons ADD fcode1' *)
        intro fstack.
        setoid_rewrite def_append_Cons...
        (* Check wether there are enough values in the stack for addition. *)
        destruct fstack as [ [ | fv1 [ [ | fv2 fstack2 ] | ] ] | ]...
        1,2: (* If there are not at least two values, the result is undefined. *)
             autodef.
        1,2: rewrite exec_strict_on_stack_arg...
        * (* If there are to values, we can use the definition of [exec]. *)
          setoid_rewrite def_exec_ADD...
          (* Finish proof with induction. *)
          induction fcode1' as [ code1' | sCode1' pfCode1' IHpfCode1' ] using Free_Ind...
          { autoIH; apply IH. }
          { autodef.
            rewrite exec_strict_on_stack_arg... }
        * (* If the stack is [Nothing] after the first value, the result is [Nothing]. *)
          autodef.
          rewrite exec_strict_on_stack_arg...
        * (* If the stack is [Nothing], the result is also be [Nothing]. *)
          autodef.
          rewrite exec_strict_on_stack_arg...
      + (* fcode1 = Cons Nothing fcode1' *)
        (* If the operation is [Nothing] the result is also [Nothing]. *)
        intro fstack.
        autodef.
        rewrite exec_strict_on_stack_arg...
    - (* fcode1 = Nothing *)
      (* If the code is [Nothing] the result is also [Nothing]. *)
      intro fstack.
      autodef.
      rewrite exec_strict_on_stack_arg...
  Qed.

  (* To prove the correctness of the compiler [comp] as stated in the QuickCheck property,
     we have to generalize it first by adding an additional recursively pure stack and we
     need the precondition, that the given expression is recursively pure. *)
  Lemma comp_correct' :
    forall (fexpr : Free Shape Pos (Expr Shape Pos)),
    RecPureExpr fexpr ->
    forall (fstack : Free Shape Pos (Stack Shape Pos)),
    RecPureStack fstack ->
        exec Part (comp fexpr) fstack
        = Cons (eval fexpr) fstack.
  Proof with (pretty).
    intros fexpr HPureE.
    destruct fexpr as [ expr | ] using Free_Ind; [ | dependent destruction HPureE ]...
    induction expr as [ fn | fx fy IHfx IHfy ] using Expr_Ind...
    + (* Expr = Val fn *)
      intros fstack HPureS.
      setoid_rewrite def_comp_Val...
      setoid_rewrite def_eval_Val...
      destruct fstack as [ stack | ]; [ | dependent destruction HPureS ]...
      setoid_rewrite def_exec_PUSH...
      setoid_rewrite def_exec_Nil...
      reflexivity.
    + (* Expr = Add fx fy *)
      intros fstack HPureS.
      dependent destruction HPureE.
      destruct fx as [ x | ]; [ | dependent destruction HPureE1 ]...
      simplify IHfx as IHx.
      destruct fy as [ y | ]; [ | dependent destruction HPureE2 ]...
      simplify IHfy as IHy.
      setoid_rewrite def_eval_Add...
      setoid_rewrite def_comp_Add...
      rewrite exec_append...
      rewrite exec_append...
      setoid_rewrite (IHx HPureE1 _ HPureS)...
      rewrite (IHy HPureE2 _ (recPureStack_cons _ _ HPureS)).
      setoid_rewrite def_exec_ADD...
      setoid_rewrite def_exec_Nil...
      reflexivity.
  Qed.

  (* The theorem derived by the correctness QuickCheck property for comp_correct
     can now be proven with the more general lemma above and under the that the
     given expression is recursively pure. *)
  Lemma comp_correct :
    forall (fexpr : Free Shape Pos (Expr Shape Pos)),
    RecPureExpr fexpr ->
        quickCheck (prop_comp_correct Shape Pos Part fexpr).
  Proof.
    simpl; intros fexpr HPure.
    apply (comp_correct' fexpr HPure Nil recPureStack_nil).
  Qed.

  (* To prove the equivalence property of the two compilers [comp] and [comp'] we first prove the
     derived property for [comp] and [compApp] which is used by [comp']. *)
  Lemma compApp_comp_append_eq :
    forall (fexpr : Free Shape Pos (Expr Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp fexpr fcode
        = append (comp fexpr) fcode.
  Proof with pretty.
    intro fexpr.
    destruct fexpr as [ expr | ]...
    - (* If the expression is pure, we can do an induction over it. *)
      induction expr as [ fn | fx fy IHfx IHfy ] using Expr_Ind...
      + (* expr = Val fn *)
        intro fcode.
        setoid_rewrite def_comp_Val...
        setoid_rewrite def_compApp_Val...
        setoid_rewrite def_append_Cons...
        rewrite def_append_Nil...
        reflexivity.
      + (* expr = Add fx fy *)
        intro fcode.
        setoid_rewrite def_comp_Add...
        rewrite <- append_assocs.
        setoid_rewrite def_append_Cons...
        rewrite def_append_Nil...
        setoid_rewrite def_compApp_Add...
        destruct fy as [ y | ]; destruct fx as [ x | ]...
        * (* Both sub-expressions are pure *)
          simplify IHfy as IHy.
          simplify IHfx as IHx.
          rewrite IHy.
          rewrite IHx.
          rewrite append_assocs.
          reflexivity.
        * (* fx = Nothing *)
          autodef.
        * (* fy = Nothing *)
          simplify IHfx as IHx.
          rewrite IHx.
          autodef.
          rewrite <- append_assocs.
          autodef.
        * (* fx = fy = Nothing *)
          autodef.
    - (* fexpr = Nothing *)
      intro fcode.
      autodef.
   Qed.

 (* With the equivalence lemma above the proof of the main equivalence theorem is simple. *)
 Lemma comp_comp'_eq : quickCheck (prop_comp_comp'_eq Shape Pos).
  Proof with pretty.
    simpl; intro fexpr.
    rewrite def_comp'.
    rewrite compApp_comp_append_eq.
    rewrite append_nil.
    reflexivity.
  Qed.

  (* The correctness of the compiler [comp'] is implied by the equivalence to
     the compiler [comp] and the correctness of [comp]. *)
  Lemma comp'_correct : 
    forall (fexpr : Free Shape Pos (Expr Shape Pos)),
    RecPureExpr fexpr ->
        quickCheck (prop_comp'_correct Shape Pos Part fexpr).
  Proof.
    simpl.
    intros fexpr HPure.
    rewrite <- comp_comp'_eq.
    apply (comp_correct fexpr HPure).
  Qed.

End Proofs.
