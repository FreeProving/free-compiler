(* This file contains the tactic [prove_forall] that proofs such a the
   [ForallT_a_forall] lemmas for datatypes.
   For each type variable [a] of each datatype [T] that has strong induction
   schemes, there should be the inductive properties [ForT_a] and [InT_a] as
   well as a lemma [ForT_a_forall] that states the connection between these
   values. *)

From Base Require Import Free.ForFree.

Require Import Coq.Program.Equality.

Ltac forall_ForType_InType forType inType forType_forall :=
  match goal with
    | [ HF : forType _ ?fx
      , HI : inType ?x ?fx
    |- _ ] =>
      rewrite forType_forall in HF;
      specialize (HF x HI)
  end.

Ltac forall_ForFree_InFree :=
  match goal with
    | [ HF : ForFree ?Shape ?Pos ?T _ ?fx
      , HI : InFree ?Shape ?Pos ?T ?x ?fx
    |- _ ] =>
      rewrite ForFree_forall in HF;
      specialize (HF x HI)
  end.

Ltac forall_trivial :=
  match goal with
  | [ H : ?P |- ?P ] => apply H
  end.

Ltac forall_trivial_imp2 :=
  match goal with
  | [ HImp : ?TF -> ?TI -> ?P
    , HF : ?TF
    , HI : ?TI
    |- ?P ] =>
    apply (HImp HF HI)
  end.

Hint Extern 0 => forall_trivial : prove_forall_db.
Hint Extern 0 => forall_trivial_imp2 : prove_forall_db.
Hint Extern 0 => forall_ForFree_InFree : prove_forall_db.

Ltac prove_forall Ind :=
     repeat (match goal with
             | [ |- forall (_ : _ -> Prop), _ ] => intro
             end);
     let C  := fresh "C"
  in let HF := fresh "HF"
  in let x  := fresh "x"
  in let HI := fresh "HI"
  in let H  := fresh "H"
  in intro C; split;
     [ intro HF;
       repeat split;
       intros x HI;
       induction C using Ind;
       dependent destruction HI;
       dependent destruction HF;
       auto with prove_forall_db
     | intro H;
       repeat (match goal with
               | [H1 : _ /\ _ |- _] => destruct H1
               end);
       induction C using Ind;
       constructor;
       auto with prove_forall_db2
     ].

Ltac forall_ForType forType forType_forall :=
  match goal with
  | [ HF : forType _ ?fx
    |- forType _ ?fx ] =>
       let x  := fresh "x"
    in let HI := fresh "HI"
    in apply forType_forall; intros x HI;
       rewrite forType_forall in HF;
       specialize (HF x HI)
  | [ H : forall y : ?A, _ |- forType ?P ?fx ] =>
       let x  := fresh "x"
    in let HI := fresh "HI"
    in apply forType_forall; intros x HI;
       specialize (H x)
  end.

Ltac forall_ForFree :=
  match goal with
  | [ HF : ForFree ?Shape ?Pos ?T _ ?fx
    |- ForFree ?Shape ?Pos ?T _ ?fx ] =>
       let x  := fresh "x"
    in let HI := fresh "HI"
    in apply ForFree_forall; intros x HI;
       rewrite ForFree_forall in HF;
       specialize (HF x HI)
  | [ H : forall y : ?A, _ |- ForFree ?Shape ?Pos ?T ?P ?fx ] =>
       let x  := fresh "x"
    in let HI := fresh "HI"
    in apply ForFree_forall; intros x HI;
       specialize (H x)
  end.

Ltac forall_finish :=
  match goal with
  | [ H : ?TI -> ?P |- ?P ] =>
    apply H; constructor; trivial
  end.

Hint Extern 0 => forall_finish : prove_forall_db2.
Hint Extern 0 => forall_trivial : prove_forall_db2.
Hint Extern 0 => forall_ForFree : prove_forall_db2.

Ltac forall_finish2 Con :=
  match goal with
  | [ H1 : (forall y : ?A, _ -> ?P y) -> ?TF ?P ?C
    , H2 : forall z : ?A, _ -> ?P z
    |- ?TF ?P ?C ] =>
       let x  := fresh "x"
    in let HI := fresh "HI"
    in apply H1; intros x HI; apply H2; eauto using Con
  end.
