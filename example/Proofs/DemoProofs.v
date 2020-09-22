From Base Require Import Free Handlers.
From Base Require Import Prelude.
From Base Require Import Test.QuickCheck.

From Generated Require Import Demo.

Require Import Coq.Lists.List.
Import List.ListNotations.

(* 
doubleRoot l = root l + root l

tracedTree = Node (trace "Root" 1) undefined

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

(* Call-by-value evaluation. Immediately simplifies to ~ False
   due to strict evaluation of ==='s  arguments. *)
Theorem prop_cbv : ~ quickCheckHandle 
  (prop_double_root_traced _ _ Cbv _ _)
  HandlerMaybeShareTrace.
Proof. simpl; unfold Search.collectMessages; simpl.
discriminate. Qed.

(*
(* doubleRoot (tracedTree) != trace "Root" 1 in a cbv setting
   with handling. *)
Theorem prop_cbv_manual : 
  @handle _ _ _ (HandlerMaybeShareTrace _)
    (doubleRoot _ _ Cbv _ (tracedTree _ _ Cbv _)) 
  <> 
  @handle _ _ _ (HandlerMaybeShareTrace _)
    (@trace _ _ _ (Integer _ _) "Root"%string (pure 2%Z)).
Proof. 
simpl; unfold Search.collectMessages; simpl.
discriminate. Qed.
*)
