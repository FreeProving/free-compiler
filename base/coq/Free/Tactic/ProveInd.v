(* This file contains tactics that help to prove induction schemes for types.
   [prove_ind] is able to do such a proof if all required instances of
   [prove_ind_prove_for_type] were added to [prove_ind_db]. *)

From Base Require Import Free.ForFree.
From Base Require Import Free.Induction.
From Base Require Import Free.Monad.

Require Import Coq.Program.Equality.

(* The hint database that contains instances of [prove_ind_prove_for_type]. *)
Create HintDb prove_ind_db.

(* This tactic is needed to prevent [prove_ind_apply_assumption] from applying
   the fixpoint hypothesis which would invalidify the proof. *)
Local Ltac prove_ind_is_fixpoint H P :=
  match type of H with
  | forall x, P x => idtac
  end.

(* This tactic is applied at the beginning of the proof of an induction scheme
   to introduce the induction hypotheses. *)
Local Ltac prove_ind_apply_assumption :=
  match goal with
  | [ H : _ |- ?P ?x ] => tryif prove_ind_is_fixpoint H P then fail else apply H; clear H
  end.

(* This tactic eliminates the monadic layer of an induction hypothesis. *)
Local Ltac prove_ind_prove_ForFree :=
  match goal with
  | [ fx : Free ?Shape ?Pos ?T |- _ ] =>
    match goal with
    | [ |- ForFree Shape Pos T ?P fx ] =>
         let x1    := fresh "x"
      in let H    := fresh "H"
      in let x2   := fresh "x"
      in let s    := fresh "s"
      in let pf   := fresh "pf"
      in let IHpf := fresh "IHpf"
      in apply ForFree_forall; intros x1 H;
         induction fx as [ x2 | s pf IHpf ] using Free_Ind;
         [ inversion H; subst; clear H
         | dependent destruction H;
           match goal with
           | [ IHpf : forall p : Pos s, InFree Shape Pos T x1 (pf p) -> P x1
             , H : exists q : Pos s, InFree Shape Pos T x1 (pf q)
             |- _ ] =>
             let p := fresh "p"
             in destruct H as [ p ]; apply (IHpf p); apply H
           end ]
    end
  end.

(* This tactic tries to finish the proof with an hypothesis with fulfilled
   preconditions. *)
Local Ltac prove_ind_apply_hypothesis H :=
  match type of H with
  | ?PC -> _ =>
    match goal with
    | [ H2 : PC |- _ ] => specialize (H H2); prove_ind_apply_hypothesis H
    end
  | _ => apply H
  end.

(* This tactic eliminates intermediate monadic layers. *)
Local Ltac prove_ind_prove_for_free_in_free :=
  match goal with
  | [ HIF : InFree ?Shape ?Pos ?T _ ?fx
    , IH  : ForFree ?Shape ?Pos ?T _ ?fx
    |- _ ] =>
    rewrite ForFree_forall in IH; prove_ind_apply_hypothesis IH
  | [ HIF : InFree ?Shape ?Pos ?T ?x ?fx
    |- ?P ?x ] =>
       let x1   := fresh "x"
    in let s    := fresh "s"
    in let pf   := fresh "pf"
    in let IHpf := fresh "IHpf"
    in induction fx as [ x1 | s pf IHpf ] using Free_Ind;
       [ inversion HIF; subst; clear HIF
       | dependent destruction HIF;
         match goal with
         | [H : exists p : Pos s, InFree Shape Pos T x (pf p) |- _ ] =>
           let p := fresh "p"
           in destruct H as [ p H ]; apply (IHpf p H)
         end
       ]
  end.

(* This tactic is instantiated for specific types and should be added to [prove_ind_db]. *)
Ltac prove_ind_prove_for_type type forType forType_forall type_induction :=
  match goal with
  | [ x : type |- _ ] =>
    match goal with
    | [ |- forType ?P x ] =>
         let y      := fresh "x"
      in let H      := fresh "H"
      in apply forType_forall;
         type_induction x;
         intros y H; inversion H; subst; clear H; try prove_ind_prove_for_free_in_free
    end
  end.

(* This tactic proves an induction scheme. *)
Ltac prove_ind :=
  match goal with
  | [ FP : forall x, ?P x |- _ ] =>
    match goal with
    | [ |- P x] => destruct x; prove_ind_apply_assumption; prove_ind_prove_ForFree;
                   auto with prove_ind_db
    end
  end.
