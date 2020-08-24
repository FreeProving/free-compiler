From Base Require Import Free Prelude Test.QuickCheck.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.

From Generated Require Import Proofs.ReverseInvolutive.

Require Import Coq.Logic.FunctionalExtensionality.

(* In order to prove that [reverse] is not involutive in a partial setting
   consider the counterexample defined in Haskell and the [Maybe] monad. *)
Example partial_reverse_non_involutive:
  ~quickCheck (@prop_reverse_involutive Maybe.Shape Maybe.Pos).
Proof.
  simpl. intros H.
  discriminate (H unit (reverse_involutive_counterexample Maybe.Shape Maybe.Pos Maybe.Partial)).
Qed.

(* If we consider the [Identity] monad on the other hand, [reverse] becomes involutive.
   However, we have to prove the following lemma first. *)

Lemma total_reverse_append_singleton: 
  quickCheck (@prop_reverse_append_singleton Identity.Shape Identity.Pos).
Proof.
  intros a fxs fx.
  simpl. induction fxs using FreeList_ind 
    with (P := fun xs => property (prop_reverse_append_singleton Identity.Shape Identity.Pos (pure xs) fx)).
  - (* fxs = pure nil *) simpl. reflexivity.
  - (* fxs = pure (cons fxs1 fxs2) *)
    simpl. destruct fxs2 as [xs2 | s pf].
    + (* fxs2 = pure xs2 *)    simpl in *. unfold reverse in IHfxs1. rewrite IHfxs1. reflexivity.
    + (* fxs2 = impure s pf *) destruct s.
  - (* fxs = pure xs *)    apply IHfxs.
  - (* fxs = impure _ _ *) destruct s.
Qed.

Theorem total_reverse_involutive:
  quickCheck (@prop_reverse_involutive Identity.Shape Identity.Pos).
Proof.
  intros a fxs.
  simpl. induction fxs using FreeList_ind 
    with (P := fun xs => property (prop_reverse_involutive Identity.Shape Identity.Pos (pure xs))).
  - (* fxs = pure nil *) 
    simpl. reflexivity.
  - (* fxs = pure (cons fxs1 fxs2) *) 
    simpl. rewrite total_reverse_append_singleton. 
    do 2 apply f_equal. destruct fxs2 as [xs2 | s pf].
    + (* fxs2 = pure xs2 *)    simpl. apply IHfxs1.
    + (* fxs2 = impure s pf *) destruct s.
  - (* fxs = pure xs *)
    simpl. apply IHfxs.
  - (* fxs = impure s pf *)
    destruct s.
Qed.
