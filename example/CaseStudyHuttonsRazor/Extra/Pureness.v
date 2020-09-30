(* This file defines what it means for an [Expr], a [Stack] and a piece of [Code]
   to be recursively pure. It also gives some lemmas for the pureness of the
   result of [append] and [comp]. *)

From Base Require Import Free Prelude.
From Razor.Extra Require Import Tactic.
From Generated Require Import Razor.
Import Proofs.AppendAssoc.

Require Import Coq.Program.Equality.

(* This property states that the given expression is recursively pure.
   The integers in that expression however might still be impure. *)
Inductive RecPureExpr {Shape : Type} {Pos : Shape -> Type} : Free Shape Pos (Expr Shape Pos) -> Prop :=
  | recPureExpr_val : forall (fn : Free Shape Pos (Integer.Integer Shape Pos)),
      RecPureExpr (Val Shape Pos fn)
  | recPureExpr_add : forall (fx fy : Free Shape Pos (Expr Shape Pos)),
      RecPureExpr fx -> RecPureExpr fy -> RecPureExpr (Add0 Shape Pos fx fy).
 
 (* This property states that the for a given code the list is recursively pure
    and all contained operations are pure.
    The integers in those operations however might still be impure. *)
Inductive RecPureCode {Shape : Type} {Pos : Shape -> Type} : Free Shape Pos (Code Shape Pos) -> Prop :=
   | recPureCode_nil : RecPureCode (Nil Shape Pos)
   | recPureCode_cons : forall (op : Op Shape Pos) (fcode : Free Shape Pos (Code Shape Pos)),
       RecPureCode fcode -> RecPureCode (Cons Shape Pos (pure op) fcode).
 
Inductive RecPureStack {Shape : Type} {Pos : Shape -> Type} : Free Shape Pos (Stack Shape Pos) -> Prop :=
  | recPureStack_nil : RecPureStack (Nil Shape Pos)
  | recPureStack_cons : forall (fv : Free Shape Pos (Integer Shape Pos))
                              (fstack : Free Shape Pos (Stack Shape Pos)),
      RecPureStack fstack -> RecPureStack (Cons Shape Pos fv fstack).

(* If the goal is to prove one of the above pureness properties, this tactic tries to do that. *)
Ltac prove_pureness_property :=
  match goal with
  (* Try to apply a hypothesis directly. *)
  | [ H : RecPureExpr ?fe |- RecPureExpr ?fe ] => apply H
  | [ H : RecPureCode ?fc |- RecPureCode ?fc ] => apply H
  | [ H : RecPureStack ?fs |- RecPureStack ?fs ] => apply H
  (* Try to apply base rule for pureness. *)
  | [ |- RecPureExpr (Val ?S ?P ?fn) ] => apply recPureExpr_val
  | [ |- RecPureCode (Nil ?S ?P) ] => apply recPureCode_nil
  | [ |- RecPureStack (Nil ?S ?P) ] => apply recPureStack_nil
  | [ |- RecPureExpr (pure (val ?fn)) ] => apply recPureExpr_val
  | [ |- RecPureCode (pure nil) ] => apply recPureCode_nil
  | [ |- RecPureStack (pure nil) ] => apply recPureStack_nil
  (* Try to apply inductive rule for pureness. *)
  | [ |- RecPureExpr (Add0 ?S ?P ?fx ?fy) ] =>
        apply recPureExpr_add; try prove_pureness_property
  | [ |- RecPureCode (Cons ?S ?P (pure ?op) ?fxs) ] =>
        apply recPureCode_cons; try prove_pureness_property
  | [ |- RecPureStack (Cons ?S ?P ?fv ?fxs) ] =>
        apply recPureStack_cons; try prove_pureness_property
  | [ |- RecPureExpr (pure (add0 ?fx ?fy)) ] =>
        apply recPureExpr_add; try prove_pureness_property
  | [ |- RecPureCode (pure (cons (pure ?op)) ?fxs) ] =>
        apply recPureCode_cons; try prove_pureness_property
  | [ |- RecPureStack (pure (cons ?fv ?fxs)) ] =>
        apply recPureStack_cons; try prove_pureness_property
  (* Try to apply inductive rule for pureness on a hypothesis. *)
  | [ H : RecPureExpr (Add0 ?S ?P ?fx ?fy) |- RecPureExpr ?fe ] =>
        dependent destruction H; try prove_pureness_property
  | [ H : RecPureCode (Cons ?S ?P ?fop ?fxs) |- RecPureCode ?fc ] =>
        dependent destruction H; try prove_pureness_property
  | [ H : RecPureStack (Cons ?S ?P ?fv ?fxs) |- RecPureStack ?fs ] =>
        dependent destruction H; prove_pureness_property
  | [ H : RecPureExpr (pure (add0 ?fx ?fy)) |- RecPureExpr ?fe ] =>
        dependent destruction H; try prove_pureness_property
  | [ H : RecPureCode (pure (cons ?fop ?fxs)) |- RecPureCode ?fc ] =>
        dependent destruction H; try prove_pureness_property
  | [ H : RecPureStack (pure (cons ?fv ?fxs)) |- RecPureStack ?fs ] =>
        dependent destruction H; prove_pureness_property
  end.

(* If we have an assumption that a pureness property holds for something impure,
   we can finish the proof. *)
Ltac eliminate_pureness_property_impure :=
  match goal with
  (* Try to destruct a pureness property over an impure value. *)
  | [ H : RecPureExpr (impure ?s ?pf) |- _ ] => dependent destruction H
  | [ H : RecPureCode (impure ?s ?pf) |- _ ] => dependent destruction H
  | [ H : RecPureCode (Cons ?S ?P (impure ?s ?pf) ?fxs) |- _ ] => dependent destruction H
  | [ H : RecPureCode (pure (cons ?S ?P (impure ?s ?pf) ?fxs)) |- _ ] => dependent destruction H
  | [ H : RecPureStack (impure ?s ?pf) |- _ ] => dependent destruction H
  (* Try to apply inductive rule for pureness on a hypothesis. *)
  | [ H : RecPureExpr (Add0 ?S ?P ?fx ?fy) |- _ ] =>
        dependent destruction H; eliminate_pureness_property_impure
  | [ H : RecPureCode (Cons ?S ?P ?fop ?fxs) |- _ ] =>
        dependent destruction H; eliminate_pureness_property_impure
  | [ H : RecPureStack (Cons ?S ?P ?fv ?fxs) |- _ ] =>
        dependent destruction H; eliminate_pureness_property_impure
  | [ H : RecPureExpr (pure (add0 ?fx ?fy)) |- _ ] =>
        dependent destruction H; eliminate_pureness_property_impure
  | [ H : RecPureCode (pure (cons ?fop ?fxs)) |- _ ] =>
        dependent destruction H; eliminate_pureness_property_impure
  | [ H : RecPureStack (pure (cons ?fv ?fxs)) |- _ ] =>
        dependent destruction H; eliminate_pureness_property_impure
  end.

Section Lemmas.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  (* If we apply [append] on two pieces of recursively pure code the result is recursively pure code. *)
  Lemma append_pure :
    forall (fcode1 fcode2 : Free Shape Pos (Code Shape Pos)),
    RecPureCode fcode1 ->
    RecPureCode fcode2 ->
        RecPureCode (append Shape Pos fcode1 fcode2).
  Proof.
    intros fcode1 fcode2 HPure1 HPure2.
    (* The first piece of code is pure. *)
    destruct fcode1 as [ code1 | ]. 2: dependent destruction HPure1.
    (* Do an induction over the first piece of code. *)
    induction code1 as [ | fop fcode1' ] using List_ind.
    - simpl. apply HPure2.
    - (* The first operation in a non-empty [code1] is pure. *)
      destruct fop as [ op | ]. 2: do 2 dependent destruction HPure1.
      (* The rest list in a non-empty [code1] is also pure. *)
      destruct fcode1' as [ code1' | ]. 2: do 2 dependent destruction HPure1.
      simpl. apply recPureCode_cons.
      autoIH. dependent destruction HPure1. apply (IH HPure1).
  Qed.

  (* The compilation of a recursively pure expression with [comp] produces recursively pure code. *)
  Lemma comp_pure :
    forall (fexpr : Free Shape Pos (Expr Shape Pos)),
    RecPureExpr fexpr ->
        RecPureCode (comp Shape Pos fexpr).
  Proof.
    intros fexpr HPure.
    (* The given expression is pure. *)
    destruct fexpr as [ expr | sExpr pfExpr ]. 2: dependent destruction HPure.
    (* Do an induction over this expression. *)
    induction expr as [ fn | fx fy IHfx IHfy ].
    - (* In this case, we have a single value as expression. *)
      simpl. apply recPureCode_cons. apply recPureCode_nil.
    - (* In this case, we have an addition of two expressions [fx] and [fy]. *)
      dependent destruction HPure.
      (* The expression [fx] is pure. *)
      destruct fx as [ x | sX pfX ]. 2: dependent destruction HPure1.
      (* Use the lemma [append_pure] with the three recursively pure pieces of code: 
         - (comp_0 Shape Pos x)
         - (fy >>= (fun y : Expr Shape Pos => comp_0 Shape Pos y))
         - (Cons Shape Pos (ADD Shape Pos) (Nil Shape Pos)) *)
      simpl. apply append_pure. apply append_pure.
      (* Now we need to prove that those pieces of code were indeed recursively pure. *)
      + autoIH. apply (IH HPure1).
      + (* The expression [fy] is pure. *)
        destruct fy as [ y | sY pfY ]. 2: dependent destruction HPure2.
        autoIH. apply (IH HPure2).
      + apply recPureCode_cons. apply recPureCode_nil.
    Qed.

End Lemmas.
