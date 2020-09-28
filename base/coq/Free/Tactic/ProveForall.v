(* This file contains the tactic [prove_forall] that proofs such a the
   [ForallT_forall] lemmas for datatypes.
   For each datatype [T] that has type variables, there should be the inductive
   property [ForT] and for every tpe variable of that type a Property [InT_a]. 
   The lemma [ForT_forall] that states the connection between those properties.
*)

From Base Require Import Free.ForFree.

Require Import Coq.Program.Equality.

(* This is the hint database which is used by [prove_forall]. *)
Create HintDb prove_forall_db.

(* This tactic splits all hypotheses, which are conjunctions, into smaller
   hypotheses. *)
Ltac prove_forall_split_hypotheses :=
  repeat (match goal with
          | [H : _ /\ _ |- _] => destruct H
          end).

(* This tactic rewrites a 'ForT' hypothesis [HF] using a forall lemma
   [forType_forall] and specializes it using a value [x] for which an 'InT'
   hypothesis [IF] exists.
   This tactic should be instantiated for types with type variables and added to
   [prove_forall_db]. *)
Ltac prove_forall_ForType_InType HF HI x forType_forall :=
  rewrite forType_forall in HF;
  prove_forall_split_hypotheses;
  match goal with
  | [ HF1 : forall y, _ -> _ |- _ ] =>
    specialize (HF1 x HI);
    auto with prove_forall_db
  end.

(* [prove_forall_ForType_InType] instance of [Free].
   You can use this as reference for instances of
   [prove_forall_ForType_InType]. *)
Hint Extern 0 =>
  match goal with
  | [ HF : ForFree _ _ _ _ ?fx
    , HI : InFree _ _ _ ?x ?fx
    |- _ ] =>
      prove_forall_ForType_InType HF HI x ForFree_forall
  end : prove_forall_db.

(* Rewrites the goal using the given 'forall' lemma.
   This tactic should be instantiated for types with type variables and added to
   [prove_forall_db]. *)
  Ltac prove_forall_prove_ForType forType_forall :=
  rewrite forType_forall;
  repeat split;
  let x  := fresh "x"
  in let HI := fresh "HI"
  in intros x HI;
  auto with prove_forall_db.

(* [prove_forall_prove_ForType] instance of [Free]. *)
Hint Extern 0 (ForFree _ _ _ _ _) =>
  prove_forall_prove_ForType ForFree_forall : prove_forall_db.

(* Applies a hypothesis which is an implication with two fulfilled
   preconditions to prove the goal. *)
Ltac prove_forall_trivial_imp :=
  match goal with
  | [ HImp : ?TF -> ?TI -> ?P
    , HF : ?TF
    , HI : ?TI
    |- ?P ] =>
    apply (HImp HF HI)
  end.

Hint Extern 1 => prove_forall_trivial_imp : prove_forall_db.

(* Tries to prove an 'InT' property by using an constructor for that type.
   This tactic should be instantiated locally with all 'InT' constructors of a
   type with type variables and added to [prove_forall_db] when proving the
   corresponding 'forall' lemma. *)
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

(* This tactic proves a 'forall' lemma using a given induction scheme for the
   corresponding type using the database [prove_forall_db].
   The database should contain an instance of [prove_forall_finish_rtl] for
   every 'InT' constructor of that type and instances of
   [prove_forall_ForType_InType] and [prove_forall_prove_ForType] for every
   dependent type. *)
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
