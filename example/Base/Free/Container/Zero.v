(** * Container instance for the identity monad. *)

From Base Require Import Free.Container.
From Base Require Import Free.Util.Void.

Definition Zero (A : Type) := Void.

Definition S__Zero : Type := Void.
Definition P__Zero (s : S__Zero) : Type := Void.
Definition E__Zero (A : Type) : Type := Ext S__Zero P__Zero A.

Definition to__Zero {A : Type} (e : E__Zero A) : Zero A :=
  match e with
  | ext s _ => match s with end
  end.
Definition from__Zero {A : Type} (z : Zero A) : E__Zero A :=
  match z with end.

Lemma to_from__Zero: forall (A : Type) (fx : Zero A),
  to__Zero (from__Zero fx) = fx.
Proof.
  intros A fx.
  destruct fx.
Qed.

Lemma from_to__Zero: forall (A : Type) (e : E__Zero A),
  from__Zero (to__Zero e) = e.
Proof.
  intros A e.
  destruct e.
  destruct s.
Qed.

Instance C__Zero : Container Zero :=
  {
    Shape := S__Zero;
    Pos := P__Zero;
    to := @to__Zero;
    from := @from__Zero;
    to_from := to_from__Zero;
    from_to := from_to__Zero
  }.
