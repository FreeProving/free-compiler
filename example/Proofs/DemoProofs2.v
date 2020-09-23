From Base Require Import Free Handlers.
From Base Require Import Prelude.
From Base Require Import Test.QuickCheck.
From Base Require Import Free.Instance.Maybe Instance.Trace.

From Generated Require Import Demo2.

Require Import Coq.Lists.List.
Import List.ListNotations.
Open Scope Z.


(*
doubleElems :: [Integer] -> Integer
doubleElems [] = 0
doubleElems (x:xs) = x + x + doubleElems xs

prop_double_elems = doubleElems [trace "eval 1" 1, trace "eval 2" 2]
=== trace "eval 1" (trace "eval 2" 6)

*)

(* Call-by-need evaluation. *)
Theorem theorem_double_Elems_cbneed : quickCheckHandle (prop_double_Elems _ _ Cbneed _)
 HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed.

(* Call-by-name evaluation. *)
Theorem theorem_double_Elems_cbn : ~quickCheckHandle (prop_double_Elems _ _ Cbn _)
 HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
discriminate. Qed.

(* Call-by-value evaluation. *)
Theorem theorem_double_Elems_cbv : quickCheckHandle (prop_double_Elems _ _ Cbv _)
 HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed.

(* Ignore tracing log, only consider results. *)
Theorem theorem_double_Elems_cbneed_no_trace : quickCheckHandle (prop_double_Elems _ _ Cbneed
 {| trace _ _ x := x |} ) HandlerShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed.

(* Ignore tracing log, only consider results, use the minimal handler. *)
Theorem theorem_double_Elems_cbneed_no_trace_min_handler 
  : quickCheckHandle (prop_double_Elems _ _ Cbneed
     {| trace _ _ x := x |} ) HandlerShare.
Proof. simpl; unfold Search.collectMessages; simpl.
reflexivity. Qed.