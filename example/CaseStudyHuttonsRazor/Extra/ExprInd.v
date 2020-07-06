From Base Require Import Free.
From Generated Require Import Razor.

Require Import Coq.Program.Equality.

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
        induction fx as [ x | s pf IHpf ] using Free_Ind.
        * inversion IHe; subst. apply Expr_Ind.
        * dependent destruction IHe; subst. destruct H as [ p ].
          apply IHpf with (p := p). apply H.
      + apply ForFree_forall. intros e IHe.
        induction fy as [ y | s pf IHpf ] using Free_Ind.
        * inversion IHe; subst. apply Expr_Ind.
        * dependent destruction IHe; subst. destruct H as [ p ].
          apply IHpf with (p := p). apply H.
  Defined.

End Expr_ind.