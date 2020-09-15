From Base Require Import Free.ForFree.
From Base Require Import Free.Induction.
From Base Require Import Free.Monad.

Require Import Coq.Program.Equality.

Local Ltac is_fixpoint H P :=
  match type of H with
  | forall x, P x => idtac
  end.

Local Ltac prove_ind_apply_assumption :=
  match goal with
  | [ H : _ |- ?P ?x ] => tryif is_fixpoint H P then fail else apply H
  end.

Local Ltac prove_ind_prove_for_free FP :=
  match goal with
  | [ fx: Free ?Shape ?Pos ?T |- _ ] =>
    match goal with
    | [ |- ForFree Shape Pos T ?P fx ] =>
         let x1    := fresh "x"
      in let H    := fresh "H"
      in let x2   := fresh "x"
      in let s    := fresh "s"
      in let pf   := fresh "pf"
      in let IHpf := fresh "IHpf"
      in let p    := fresh "p"
      in apply ForFree_forall; intros x1 H;
         induction fx as [ x2 | s pf IHpf ] using Free_Ind;
         [ inversion H; subst; apply FP
         | dependent destruction H; subst; destruct H as [ p ];
           apply (IHpf p); apply H ]
    end
  end.

Ltac prove_ind :=
  match goal with
  | [ FP : forall y, ?P y |- ?P ?x ] =>
    destruct x; prove_ind_apply_assumption; prove_ind_prove_for_free FP
  end.
