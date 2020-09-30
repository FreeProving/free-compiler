From Base Require Import Free Free.Instance.Error Free.Instance.Maybe Prelude Test.QuickCheck.
From Generated Require Import Proofs.ConsUncons.

Require Import Coq.Logic.FunctionalExtensionality.

(* The first QuickCheck property holds for any [Partial] instance. Therefore
   its proof differs only in that way from proofs about functions that do not
   return an error, that an [Partial] instance for [Shape] and [Pos] is given. *)
Lemma cons_unconsE : quickCheck (fun Shape Pos I => @prop_cons_unconsE Shape Pos I Cbn).
Proof.
  intros Shape Pos I Partial A SA NF fx fxs.
  reflexivity.
Qed.

(* The second QuickCheck property holds provably for the [Maybe] instance of [Partial]. *)
Lemma unconsE_fst_Maybe : quickCheck (@prop_unconsE_fst 
    (Comb.Shape Share.Shape Maybe.Shape)
    (Comb.Pos Share.Pos Maybe.Pos)
    _ Cbn
    (Maybe.Partial _ _)).
Proof.
  intros A SA NF fxs.
  simpl.
  destruct fxs as [ xs | s pf ].
  - destruct xs as [ | fx1 fxs1 ].
    + simpl. unfold Nothing. f_equal. extensionality p. destruct p.
    + reflexivity.
  - simpl. f_equal. extensionality p. destruct s.
    (* Because the Share effect is required in the effect stack even though
       call-by-name evaluation is used, an impure value could theoretically consist
       of sharing syntax, even though sharing syntax is never used in this setting. *)
    + admit.
    (* The Maybe effect does not have any positions. *)
    + destruct p. Admitted.

(* But the second QuickCheck property doesn't hold for the [Error] instance of
   [Partial] as [unconsE] and [head] have different error messages on an empty
   list. *)
Lemma unconsE_fst_Error : not (quickCheck (@prop_unconsE_fst 
  (Comb.Shape Share.Shape (Error.Shape string))
  (Comb.Pos Share.Pos Error.Pos) 
   _ Cbn
  (Error.Partial _ _))).
Proof.
  intro H.
  specialize (H bool _ _ (Nil _ _)).
  discriminate H.
Qed.

Section ErrorMessages.

  (* To prove facts about the error messages we can write an abbreviation for
     an [error] with a specific message. *)
  Definition EmptyListError {A : Type} := @error _ _ (Error.Partial _ _) A "unconsE: empty list"%string.

  (* If we weren't looking for an actual [error] but for an [undefined] in Haskell
     we could use the following definition. *)
  Definition Undefined {A NF : Type} := @undefined _ _ (Error.Partial _ _) A.

  (* Now we can define and prove the lemma that using [unconsE] with an empty
     list results in an [EmptyListError] *)
  Lemma nil_unconsE_empty_list_error : forall (A NF : Type),
    @unconsE _ _ (Error.Partial _ _) A (Nil _ _) = EmptyListError.
  Proof.
    intro A.
    simpl.
    reflexivity.
  Qed.

  (* We can also prove that using [unconsE] on an non-empty list does not cause
     an [EmptyListError]. *)
  Lemma cons_unconsE_no_empty_list_error : forall (A NF : Type) (fx : Free _ _ A) (fxs : Free _ _ (List _ _ A)),
    unconsE _ _ (Error.Partial _ _) (Cons _ _ fx fxs) <> EmptyListError.
  Proof.
    intros A NF fx fxs.
    simpl.
    discriminate.
  Qed.

  (* And finally we can prove that an [EmptyListError] is the only error that
     can occur if the argument is error-free. *)
  Lemma unconsE_only_empty_list_error : forall (A NF : Type) (l : List _ _ A),
    (exists (result : Pair _ _ A (List _ _ A)), unconsE _ _ (Error.Partial _ _) (NoError _ _ l) = NoError _ _ result) \/
    (                                           unconsE _ _ (Error.Partial _ _) (NoError _ _ l) = EmptyListError).
  Proof.
    intros A NF l.
    destruct l as [ | fx fxs ].
    - right. reflexivity.
    - left. simpl. exists (pair_ fx fxs). reflexivity.
  Qed.
End ErrorMessages.
