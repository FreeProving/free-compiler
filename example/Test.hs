module Test where

import           Test.QuickCheck

append :: [a] -> [a] -> [a]
append xs ys = case xs of
  []      -> ys
  x : xs' -> x : append xs' ys

prop_append_assoc :: [a] -> [a] -> [a] -> Property
prop_append_assoc xs ys zs =
  xs `append` (ys `append` zs) === (xs `append` ys) `append` zs

{-

Class QuickCheck (A : Type) := { quickCheck : A -> Prop }.
Instance QuickCheckFunction (A : Type) (B : Type) (QCB : QuickCheck B)
  : QuickCheck (A -> B)
  := { quickCheck (f : A -> B) := forall (x : A), quickCheck (f x) }.
Instance QuickCheckForall (A : Type) (B : A -> Type) (QCB : forall (x : A), QuickCheck (B x))
  : QuickCheck (forall (x : A), B x)
  := { quickCheck (f : forall (x : A), B x) := forall (x : A), quickCheck (f x) }.
Instance QuickCheckProperty
  : QuickCheck Prop
  := { quickCheck (p : Prop) := p }.
Instance QuickCheckBool
  (Shape : Type) (Pos : Shape -> Type)
  : QuickCheck (Free Shape Pos (Bool Shape Pos))
  := { quickCheck := isPureTrue Shape Pos }.

Theorem quickCheckProperty : forall (P : Prop), P -> quickCheck P.
Proof. intros P HP. apply HP. Qed.

(******************************************************)

Require Import Coq.Logic.FunctionalExtensionality.

Lemma append_nil:
  forall (Shape : Type)
         (Pos : Shape -> Type)
         (a : Type)
         (fxs : Free Shape Pos (List Shape Pos a)),
  append Shape Pos fxs (pure nil) = fxs.
Proof.
  intros Shape Pos a fxs.
  induction fxs using FreeList_ind with (P := fun xs => append_1 Shape Pos a (pure nil) xs = pure xs); simpl.
  - reflexivity.
  - unfold Cons; simpl; repeat apply f_equal. apply IHfxs1.
  - apply IHfxs.
  - repeat apply f_equal. extensionality p. apply H.
Qed.

Lemma append_0_assoc :
  forall (Shape : Type)
         (Pos : Shape -> Type)
         {a : Type}
         (xs : List Shape Pos a)
         (fys fzs : Free Shape Pos (List Shape Pos a)),
      append_1 Shape Pos a (append Shape Pos fys fzs) xs
      = append Shape Pos (append_1 Shape Pos a fys xs) fzs.
Proof.
  intros Shape Pos a xs fys fzs.
  induction xs using List_Ind.
  - reflexivity.
  - induction fxs using Free_Ind.
    + simpl. simplify H as IH. rewrite IH. reflexivity.
    + (*Inductive case: [fxs = impure s pf] with induction hypothesis [H] *)
      simpl. do 2 apply f_equal. extensionality p.
      simplify H as IH. apply IH.
Qed.

Theorem prop_append_assoc_theorem : quickCheck prop_append_assoc.
Proof.
  intros Shape Pos a fxs fys fzs. apply quickCheckProperty. unfold prop_append_assoc.
  (* FILL In HERE *)
  induction fxs as [ | s pf IH ] using Free_Ind.
  - simpl. apply append_0_assoc.
  - (*Inductive case: [fxs = impure s pf] with induction hypothesis [IH] *)
    simpl. apply f_equal. extensionality p.
    apply IH.
Qed.


-}
