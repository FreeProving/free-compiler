From Base Require Import Free Handlers.
From Base Require Import Prelude.
From Base Require Import Test.QuickCheck.
From Base Require Import Free.Instance.Maybe Instance.Trace.

From Generated Require Import Demo.

Require Import Coq.Lists.List.
Import List.ListNotations.

(* 
doubleRoot l = root l + root l

tracedTree = Node (trace "Root" 1) [Node (traced "Child") 2 []]

Property: 
   doubleRoot tracedTree === trace "Root" 2
*)

(* Call-by-name evaluation. *)
Theorem prop_cbn : ~ quickCheckHandle 
  (prop_double_root_traced _ _ Cbn _ _)
  HandlerMaybeShareTrace.
Proof. 
simpl; unfold Search.collectMessages; simpl.
discriminate. Qed.

(* Call-by-need evaluation. *)
Theorem prop_cbneed : quickCheckHandle 
  (prop_double_root_traced _ _ Cbneed _ _)
  HandlerMaybeShareTrace.
Proof. 
simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed.

(* Call-by-value evaluation. *)
Theorem prop_cbv : ~ quickCheckHandle 
  (prop_double_root_traced _ _ Cbv _ _)
  HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
discriminate. Qed.

(* Unhandled version with call-by-need does not hold! *)
Definition S := (Comb.Comb.Shape Share.Shape (Comb.Comb.Shape Maybe.Shape Trace.Shape)).
Definition P := (Comb.Comb.Pos Share.Pos (Comb.Comb.Pos Maybe.Pos Trace.Pos)).
Theorem prop_cbneed_unhandled : ~ quickCheck 
  (prop_double_root_traced S P Cbneed _ _).
Proof.
simpl. unfold doubleRoot. simpl.
discriminate. Qed.



(*
tracedTreeP = Node (trace "Root" 1) undefined

Property: 
   doubleRoot tracedTreeP === root tracedTreeP + root tracedTreeP
*)
Theorem propP_cbn : quickCheckHandle 
  (prop_double_root_tracedP _ _ Cbn _ _)
  HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed. 

(* call-by-value with Maybe interpretation of error (error s x = Nothing) *)
Theorem propP_cbv_maybe : quickCheckHandle 
  (prop_double_root_tracedP _ _ Cbv _ _)
  HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed. 

(* call-by-value with Error effect *)
Theorem propP_cbv_error : quickCheckHandle 
  (prop_double_root_tracedP _ _ Cbv _ _)
  HandlerErrorShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed. 

(* call-by-need *)
Theorem propP_cbneed : ~ quickCheckHandle 
  (prop_double_root_tracedP _ _ Cbneed _ _)
  HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
discriminate. Qed.

(* call-by-need, ignore tracing *)
Theorem propP_cbneed_no_tracing : quickCheckHandle 
  (prop_double_root_tracedP _ _ Cbneed _ {| trace _ msg x := x |})
  HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed.

(* Ignore tracing, removed tracing handler *)
Theorem propP_cbneed_no_tracing_min_handling : quickCheckHandle 
  (prop_double_root_tracedP _ _ Cbneed _ {| trace _ msg x := x |})
  HandlerShareMaybe.
Proof. simpl.
reflexivity. Qed.


(* Unhandled *)

(* Partial example without sharing, unhandled (previous model) *)
Theorem prop_cbn_unhandled : quickCheck (fun (Shape : Type) (Pos : Shape -> Type)
  {M : Injectable Maybe.Shape Maybe.Pos Shape Pos}
  {I : Injectable Share.Shape Share.Pos Shape Pos}
  {T : Injectable Trace.Shape Trace.Pos Shape Pos}
  => prop_double_root_tracedP Shape Pos Cbn (Maybe.Partial Shape Pos) _).
Proof. intros Shape Pos M I T.
simpl. unfold doubleRoot. simpl.
reflexivity. Qed. 


Theorem theorem_double_Elems_cbneed : quickCheckHandle (prop_double_Elems _ _ Cbneed _)
 HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed.

Theorem theorem_double_Elems_cbn : ~quickCheckHandle (prop_double_Elems _ _ Cbn _)
 HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
discriminate. Qed.

Theorem theorem_double_Elems_cbv : quickCheckHandle (prop_double_Elems _ _ Cbv _)
 HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed.