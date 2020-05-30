From Base Require Import Free Free.Instance.Maybe Free.Instance.Error Test.QuickCheck Prelude.
From Generated Require Import Proofs.ConsUncons.

Require Import Coq.Logic.FunctionalExtensionality.

(* The first QuickCheck property holds for any [Partial] instance. Therefore
   its proof differs only in that way from proofs about functions that do not
   return an error, that an [Partial] instance for [Shape] and [Pos] is given. *)
Lemma cons_unconsE : quickCheck prop_cons_unconsE.
Proof.
  intros Shape Pos Partial A fx fxs.
  reflexivity.
Qed.

(* The second QuickCheck property holds provable for the [Maybe] instance of [Partial]. *)
Lemma unconsE_fst_Maybe : quickCheck (@prop_unconsE_fst Maybe.Shape Maybe.Pos Maybe.Partial).
Proof.
  intros A fxs.
  simpl.
  destruct fxs as [ xs | s pf ].
  - destruct xs as [ | fx1 fxs1 ].
    + simpl. unfold Nothing. f_equal. extensionality p. destruct p.
    + reflexivity.
  - simpl. f_equal. extensionality p. destruct p.
Qed.

(* But the second QuickCheck property doesn't hold for the [Error] instance of
   [Partial] as [unconsE] and [head] have different error messages on an empty
   list. *)
Lemma unconsE_fst_Error : not (quickCheck (@prop_unconsE_fst (Error.Shape string) Error.Pos Error.Partial)).
Proof.
  intro H.
  specialize (H bool (Nil _ _)).
  discriminate H.
Qed.

Section ErrorMessages.

  (* To prove facts about the error messages we can write an abbreviation for
     an [error] with a specific message. *)
  Definition EmptyListError {A : Type} := @error _ _ _ A "uncons: empty list"%string.

  (* If we weren't looking for an actual [error] but for an [undefined] in haskell
     we could use the following definition. *)
  Definition Undefined {A : Type} := @undefined _ _ _ A.

  (* Now we can define and prove the lemma that using [unconsE] with an empty
     list results in an [EmptyListError] *)
  Lemma nil_unconsE_empty_list_error : forall (A : Type),
  @unconsE _ _ _ A (Nil _ _) = EmptyListError.
  Proof.
    intro A.
    simpl.
    reflexivity.
  Qed.

  (* We can also prove that using [unconsE] on an non-empty list does not cause
     an [EmptyListError]. *)
  Lemma cons_unconsE_no_empty_list_error : forall (A : Type) (fx : Free _ _ A) (fxs : Free _ _ (List _ _ A)),
    unconsE _ _ _ (Cons _ _ fx fxs) <> EmptyListError.
  Proof.
    intros A fx fxs.
    simpl.
    discriminate.
  Qed.

  (* And finally we can prove that an [EmptyListError] is the only error that
     can occur if the argument is error-free. *)
  Lemma unconsE_only_empty_list_error : forall (A : Type) (l : List _ _ A),
    (exists (result : Pair _ _ A (List _ _ A)), unconsE _ _ _ (NoError l) = NoError result) \/
    (                                           unconsE _ _ _ (NoError l) = EmptyListError).
  Proof.
    intros A l.
    destruct l as [ | fx fxs ].
    - right. reflexivity.
    - left. simpl. exists (pair_ fx fxs). reflexivity.
  Qed.
End ErrorMessages.
