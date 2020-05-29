From Base Require Import Free Free.Instance.Error Test.QuickCheck Prelude.
From Generated Require Import Proofs.ConsUncons.

(* The proof for the QuickCheck property differs only in that way from proofs
   about functions that do not return an error, that an [Partial] instance for
   [Shape] and [Pos] is given. *)
Lemma cons_unconsE : quickCheck prop_cons_unconsE.
Proof.
  intros Shape Pos Partial A fx fxs.
  reflexivity.
Qed.

Section ErrorMessages.

  (* To prove facts about the error messages we can write an abbreviation for
     an [error] with a specific message. *)
  Open Scope string_scope.
  Definition EmptyListError {A : Type} := @error _ _ _ A "uncons: empty list".
  Close Scope string_scope.

  (* If we weren't looking for an actual [error] but for an [undefined] in haskell
     we could use the following definition. *)
  Open Scope string_scope.
  Definition Undefined {A : Type} := @undefined _ _ _ A.
  Close Scope string_scope.

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
  Lemma cons_uncons_no_empty_list_error : forall (A : Type) (fx : Free _ _ A) (fxs : Free _ _ (List _ _ A)),
    unconsE _ _ _ (Cons _ _ fx fxs) <> EmptyListError.
  Proof.
    intros A fx fxs.
    simpl.
    discriminate.
  Qed.

  (* And finally we can prove that an [EmptyListError] is the only error that
     can occur if the argument is error-free. *)
  Lemma uncons_only_empty_list_error : forall (A : Type) (l : List _ _ A),
    (exists (result : Pair _ _ A (List _ _ A)), unconsE _ _ _ (NoError l) = NoError result) \/
    (                                           unconsE _ _ _ (NoError l) = EmptyListError).
  Proof.
    intros A l.
    destruct l as [ | fx fxs ].
    - right. reflexivity.
    - left. simpl. exists (pair_ fx fxs). reflexivity.
  Qed.
End ErrorMessages.