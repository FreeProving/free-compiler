From Base Require Import Free Handlers Prelude Test.QuickCheck.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.

From Generated Require Import Proofs.ReverseInvolutive.

Require Import Coq.Logic.FunctionalExtensionality.

(*
This counterexample does not actually work anymore when the program
is handled because the normalization done before handling introduces
strictness.
Therefore, the dummy handler NoHandler is used here, which simply
returns the program as-is.
*)
(* In order to prove that [reverse] is not involutive in a partial setting
   consider the counterexample defined in Haskell and the [Maybe] monad. *)

Example partial_reverse_non_involutive:
  ~quickCheckHandle (@prop_reverse_involutive Maybe.Shape Maybe.Pos) (NoHandler _ _).
Proof.
  simpl. intros H.
  discriminate 
    (H unit _
     (reverse_involutive_counterexample _ _ _)).
Qed.

(* If we consider the [Identity] monad on the other hand, [reverse] becomes involutive.
   However, we have to prove the following lemma first. *)

Lemma total_reverse_append_singleton: 
  quickCheckHandle (@prop_reverse_append_singleton Identity.Shape Identity.Pos) (NoHandler _ _).
Proof.
  intros a NF fxs fx.
  simpl. induction fxs using FreeList_ind 
    with (P := fun xs => toProperty (prop_reverse_append_singleton Identity.Shape Identity.Pos (pure xs) fx) (NoHandler _ _)).
  - (* fxs = pure nil *) simpl. reflexivity.
  - (* fxs = pure (cons fxs1 fxs2) *)
    simpl. destruct fxs2 as [xs2 | s pf].
    + (* fxs2 = pure xs2 *)  simpl in *. unfold reverse in IHfxs1. rewrite IHfxs1. reflexivity.
    + (* fxs2 = impure s pf *) destruct s.
  - (* fxs = pure xs *) simpl in IHfxs. apply IHfxs.
  - (* fxs = impure _ _ *) destruct s.
Qed.

Theorem total_reverse_involutive:
  quickCheckHandle (@prop_reverse_involutive Identity.Shape Identity.Pos) (NoHandler _ _).
Proof.
  intros a NF fxs.
  simpl. induction fxs using FreeList_ind 
    with (P := fun xs => toProperty (prop_reverse_involutive Identity.Shape Identity.Pos (pure xs)) (NoHandler _ _)).
  - (* fxs = pure nil *) 
    simpl. reflexivity.
  - (* fxs = pure (cons fxs1 fxs2) *) 
    specialize (total_reverse_append_singleton) as H. simpl in *.
    specialize (H a NF). rewrite H.
    do 2 apply f_equal. destruct fxs2 as [xs2 | s pf].
    + (* fxs2 = pure xs2 *)    simpl. apply IHfxs1.
    + (* fxs2 = impure s pf *) destruct s.
  - (* fxs = pure xs *)
    simpl. apply IHfxs.
  - (* fxs = impure s pf *)
    destruct s.
Qed.
