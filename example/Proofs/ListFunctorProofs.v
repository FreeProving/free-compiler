From Base Require Import Free Prelude Test.QuickCheck.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.

From Generated Require Import Proofs.ListFunctor.

Require Import Coq.Logic.FunctionalExtensionality.

(* If you want to proof a QuickCheck property for every effect,
   just apply [quickCheck] *)
Theorem prop_map_id_theorem : quickCheck prop_map_id.
Proof.
  simpl. intros Shape Pos t0. unfold Data.Function.id.
  apply f_equal. extensionality fxs.
  induction fxs using FreeList_ind
    with (P := fun xs => Data.List.map Shape Pos (pure (fun x => x)) (pure xs) = pure xs).
  - (* fxs = pure nil *)              simpl. reflexivity.
  - (* fxs = pure (cons fxs1 fxs2) *) simpl. do 2 apply f_equal. apply IHfxs1.
  - (* fxs = pure xs *)               simpl. apply IHfxs.
  - (* fxs = impure s pf *)           simpl. apply f_equal. extensionality p. apply H.
Qed.

(* If you want to proof the QuickCheck property for specific effetcs, simply
   pass [Shape] and [Pos] explicitly to the QuickCheck property and apply
   [quickCheck] as usual.
   In this case we can reuse the proof from above, because the functor law
   holds for lists regardless of the effect. *)
Theorem prop_map_id_total : quickCheck (@prop_map_id Identity.Shape Identity.Pos).
Proof. apply prop_map_id_theorem. Qed.

Theorem prop_map_id_partial : quickCheck (@prop_map_id Maybe.Shape Maybe.Pos).
Proof. apply prop_map_id_theorem. Qed.
