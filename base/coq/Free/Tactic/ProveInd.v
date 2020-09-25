(* This file contains tactics that help to prove induction schemes for types.
   [prove_ind] is able to do such a proof if all required instances of
   [prove_ind_prove_for_type] were added to [prove_ind_db]. *)

From Base Require Import Free.ForFree.
From Base Require Import Free.Induction.
From Base Require Import Free.Monad.

Require Import Coq.Program.Equality.

(* The hint database that contains instances of [prove_ind_prove_for_type]. *)
Create HintDb prove_ind_db.

(* Trivial property *)
Definition NoProperty {A : Type} : A -> Prop := fun _ => True.
Hint Extern 0 (NoProperty _) => unfold NoProperty; constructor : prove_ind_db.

(* This tactic is applied at the beginning of the proof of an induction scheme
   to select the correct hypothesis for the current induction case. *)
Ltac prove_ind_select_case FP :=
  match goal with
  | [ H : ?T |- _ ] =>
    lazymatch type of FP with
    | T => fail
    | _ => apply H; clear H
    end
  end.

(* This tactic eliminates the monadic layer of an induction hypothesis. *)
Ltac prove_ind_prove_ForFree :=
  match goal with
  | [ fx : Free ?Shape ?Pos ?T |- _ ] =>
    match goal with
    | [ |- ForFree Shape Pos T ?P fx ] =>
      apply ForFree_forall;
      let x1   := fresh "x"
      in let H := fresh "H"
      in intros x1 H;
      let x2   := fresh "x"
      in let s    := fresh "s"
      in let pf   := fresh "pf"
      in let IHpf := fresh "IHpf"
      in induction fx as [ x2 | s pf IHpf ] using Free_Ind;
      [ inversion H; subst; clear H
      | dependent destruction H;
        match goal with
        | [ IHpf : forall p : Pos s, InFree Shape Pos T ?x1 (pf p) -> P ?x1
          , H : exists q : Pos s, InFree Shape Pos T ?x1 (pf q)
          |- _ ] =>
          let p := fresh "p"
          in destruct H as [ p H ];
             apply (IHpf p H)
        end ]
    end
  end.

(* This tactic tries to finish the proof with an hypothesis with fulfilled
  preconditions. *)
Ltac prove_ind_apply_hypothesis H :=
 match type of H with
 | ?PC -> _ =>
   match goal with
   | [ H2 : PC |- _ ] => specialize (H H2); prove_ind_apply_hypothesis H
   end
 | _ => apply H
 end.

(* This tactic eliminates intermediate monadic layers. *)
Ltac prove_ind_prove_ForFree_InFree :=
 match goal with
 | [ HIF : InFree ?Shape ?Pos ?T _ ?fx
   , IH  : ForFree ?Shape ?Pos ?T _ ?fx
   |- _ ] =>
   rewrite ForFree_forall in IH; prove_ind_apply_hypothesis IH
 | [ HIF : InFree ?Shape ?Pos ?T ?x ?fx
   |- ?P ?x ] =>
   let x1      := fresh "x"
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
Ltac prove_ind_prove_ForType x forType_forall type_ind :=
  apply forType_forall;
  repeat split;
  induction x using type_ind;
  let y    := fresh "y"
  in let H := fresh "H"
  in intros y H; inversion H; subst; clear H;
  prove_ind_prove_ForFree_InFree.

(* This tactic is instantiated for specific types and should be added to [prove_ind_db]. *)
(*Ltac prove_ind_prove_ForType x type_induction :=
  induction x using type_induction;
  constructor;
  prove_ind_prove_ForFree.*)

(* This tactic proves an induction scheme. *)
Ltac prove_ind :=
  match goal with
  | [ FP : forall y, ?P y |- ?P ?x ] =>
    destruct x;
    prove_ind_select_case FP;
    prove_ind_prove_ForFree;
    intuition auto with prove_ind_db
  end.
