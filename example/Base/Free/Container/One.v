(** * Container instance for the maybe monad. *)

From Base Require Import Free.Container.
From Base Require Import Free.Util.Void.

(* The proof for `from_to__One` requires the use of the axiom of functional
   extensionallity *)
Require Import Coq.Logic.FunctionalExtensionality.

Definition One (A : Type) : Type := unit.

Definition S__One : Type := unit.
Definition P__One (s : S__One) : Type := Void.
Definition E__One (A : Type) : Type := Ext S__One P__One A.

Definition to__One {A : Type} (e : E__One A) : One A := tt.
Definition from__One {A : Type} (z : One A) : E__One A :=
  ext tt (fun p : P__One tt => match p with end).

Lemma to_from__One : forall (A : Type) (ox : One A),
  to__One (from__One ox) = ox.
Proof.
  intros A ox.
  destruct ox.
  unfold from__One.
  unfold to__One.
  reflexivity.
Qed.

Lemma from_to__One : forall (A : Type) (e : E__One A),
  from__One (to__One e) = e.
Proof.
  intros A e.
  destruct e.
  destruct s.
  unfold to__One.
  unfold from__One.
  apply f_equal.
  extensionality p.
  destruct p.
Qed.

Instance C__One : Container One :=
  {
    Shape := S__One;
    Pos := P__One;
    to := @to__One;
    from := @from__One;
    to_from := to_from__One;
    from_to := from_to__One
  }.
