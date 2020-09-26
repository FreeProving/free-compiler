(* This file contains the tactic [prove_forall] that proofs such a the
   [ForallT_a_forall] lemmas for datatypes.
   For each type variable [a] of each datatype [T] that has strong induction
   schemes, there should be the inductive properties [ForT_a] and [InT_a] as
   well as a lemma [ForT_a_forall] that states the connection between these
   values. *)

From Base Require Import Free.ForFree.

Require Import Coq.Program.Equality.

Create HintDb prove_ind_db.

Ltac prove_forall_split_hypotheses :=
  repeat (match goal with
          | [H : _ /\ _ |- _] => destruct H
          end).

Ltac prove_forall_ForType_InType HF HI x forType_forall :=
  rewrite forType_forall in HF;
  prove_forall_split_hypotheses;
  match goal with
  | [ HF1 : forall y, _ -> _ |- _ ] =>
    specialize (HF1 x HI);
    auto with prove_forall_db
  end.

Hint Extern 0 =>
  match goal with
  | [ HF : ForFree _ _ _ _ ?fx
    , HI : InFree _ _ _ ?x ?fx
    |- _ ] =>
      prove_forall_ForType_InType HF HI x ForFree_forall
  end : prove_forall_db.

Ltac prove_forall_prove_ForType forType_forall :=
  rewrite forType_forall;
  repeat split;
  let x  := fresh "x"
  in let HI := fresh "HI"
  in intros x HI;
  auto with prove_forall_db.

Hint Extern 0 (ForFree _ _ _ _ _) =>
  prove_forall_prove_ForType ForFree_forall : prove_forall_db.

Ltac prove_forall_trivial_imp :=
  match goal with
  | [ HImp : ?TF -> ?TI -> ?P
    , HF : ?TF
    , HI : ?TI
    |- ?P ] =>
    apply (HImp HF HI)
  end.

Hint Extern 1 => prove_forall_trivial_imp : prove_forall_db.

Ltac prove_forall_finish_rtl Con :=
  match goal with
  | [ H : (forall y, _ -> ?P y) -> _
    |- _ ] =>
      apply H;
      let x  := fresh "x"
      in let HI := fresh "HI"
      in intros x HI;
      auto with prove_forall_db
  | [ H : forall y, ?TI -> ?P y |- ?P ?x ] =>
    apply H;
    eapply Con;
    eauto
  end.

Hint Extern 1 => prove_forall_finish_rtl : prove_forall_db.

Ltac prove_forall type_ind :=
  let C := fresh "C"
  in intro C; split;
  [ let HF := fresh "HF"
    in intro HF;
    repeat split;
    let x  := fresh "x"
    in let HI := fresh "HI"
    in intros x HI;
    induction C using type_ind;
    dependent destruction HI;
    dependent destruction HF;
    auto with prove_forall_db
  | let H  := fresh "H"
    in intro H;
    prove_forall_split_hypotheses;
    induction C using type_ind;
    constructor;
    auto with prove_forall_db
  ].
