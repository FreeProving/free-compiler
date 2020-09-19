From Base Require Import Free Prelude Test.QuickCheck.
From Generated Require Import Proofs.AppendAssoc.

Require Import Coq.Logic.FunctionalExtensionality.

(* This lemma can be generated from a QuickCheck property. *)
Lemma append_nil : quickCheck prop_append_nil.
Proof.
  intros Shape Pos a NF fxs handler.
  simpl. f_equal.
  induction fxs using FreeList_ind with (P := fun xs => append1 Shape Pos a (pure nil) xs = pure xs); simpl.
  - reflexivity.
  - simpl; repeat apply f_equal. apply IHfxs1.
  - apply IHfxs.
  - repeat apply f_equal. extensionality p. apply H.
Qed.

(* This lemma must be written manually since it involves a helper function that is
   generated during compilation and is not visible to the original Haskell module. *)
Lemma append1_assoc :
  forall (Shape : Type)
         (Pos : Shape -> Type)
         {a : Type}
         (xs : List Shape Pos a)
         (fys fzs : Free Shape Pos (List Shape Pos a)),
      append1 Shape Pos a (append Shape Pos fys fzs) xs
      = append Shape Pos (append1 Shape Pos a fys xs) fzs.
Proof.
  intros Shape Pos a xs fys fzs.
  induction xs using List_Ind.
  - reflexivity.
  - induction fxs using Free_Ind.
    + simpl. simplify H as IH. rewrite IH. reflexivity.
    + (*Inductive case: [fxs = impure s pf] with induction hypothesis [H] *)
      simpl. do 3 apply f_equal. extensionality p.
      simplify H as IH. apply IH.
Qed.

(* Now we can prove the actual property. *)
Theorem append_assocs: quickCheck prop_append_assoc.
Proof.
  intros Shape Pos a NF fxs fys fzs handler.
  simpl. f_equal.
  induction fxs as [ | s pf IH ] using Free_Ind.
  - simpl. apply append1_assoc.
  - (*Inductive case: [fxs = impure s pf] with induction hypothesis [IH] *)
    simpl. apply f_equal. extensionality p.
    apply IH.
Qed.
