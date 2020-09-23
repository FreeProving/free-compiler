From Base Require Import Free Handlers.
From Base Require Import Prelude.
From Base Require Import Test.QuickCheck.
From Base Require Import Free.Instance.Maybe Instance.Trace.

From Generated Require Import Demo.

Require Import Coq.Lists.List.
Import List.ListNotations.
Open Scope Z.
Open Scope string.

(* 
doubleRoot l = root l + root l

tracedTreeP = Node (trace "Root" 1) undefined

Property: 
   doubleRoot tracedTreeP === root tracedTreeP + root tracedTreeP
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


(* Alternative effect interpretations *)

(* Call-by-name evaluation, ignore tracing messages. *)
Theorem prop_cbn_no_tracing_min_handler : quickCheckHandle 
  (prop_double_root_traced _ _ Cbn _ {| trace _ _ x := x |})
  HandlerShareMaybe.
Proof. 
simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed.

(* call-by-value, use Error instead of Maybe for partiality. *)
Theorem propP_cbv_error : ~ quickCheckHandle 
  (prop_double_root_traced _ _ Cbv _ _)
  HandlerErrorShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
discriminate. Qed. 







(* Unhandled version with call-by-need does not hold! *)
Definition S := (Comb.Comb.Shape Share.Shape (Comb.Comb.Shape Maybe.Shape Trace.Shape)).
Definition P := (Comb.Comb.Pos Share.Pos (Comb.Comb.Pos Maybe.Pos Trace.Pos)).
Theorem prop_cbneed_unhandled : ~ quickCheck 
  (prop_double_root_traced S P Cbneed _ _).
Proof.
simpl; unfold doubleRoot. simpl.
discriminate. Qed.















































(* Optional



tracedTree = Node (trace "Root" 1) [Node (traced "Child") 2 []]

Property: 
   doubleRoot tracedTree === trace "Root" 2


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

(* Call-by-name evaluation, tracing messages not considered, minimal handler. *)
Theorem prop_cbn_no_tracing_min_handler : quickCheckHandle 
  (prop_double_root_traced _ _ Cbn _ {| trace _ _ x := x |})
  HandlerShareMaybe.
Proof. 
simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed.

(*

(* Partial example without sharing, unhandled (previous model) *)
Theorem prop_cbn_unhandled : quickCheck (fun (Shape : Type) (Pos : Shape -> Type)
  {M : Injectable Maybe.Shape Maybe.Pos Shape Pos}
  {I : Injectable Share.Shape Share.Pos Shape Pos}
  {T : Injectable Trace.Shape Trace.Pos Shape Pos}
  => prop_double_root_tracedP Shape Pos Cbn (Maybe.Partial Shape Pos) _).
Proof. intros Shape Pos M I T.
simpl. unfold doubleRoot. simpl.
reflexivity. Qed. 

*)

*)