(** Definition of choice trees and the depth-first search algorithm,
    as well as lists where entries have IDs and a function that filters
    out entries with duplicate IDs. *)

From Base Require Import Free.Util.Sharing.
Require Import EqNat.
Require Import Coq.Strings.String.

Set Implicit Arguments.

(* Definition of a choice tree *)
Inductive Tree A :=
| Empty  : Tree A
| Leaf   : A -> Tree A
| Branch : option ID -> Tree A -> Tree A -> Tree A.

Inductive Decision := L | R.

(* ID equality *)
Definition beqId (id1 id2 : ID) : bool :=
  match id1,id2 with
  | (n11, n12, n13), (n21, n22, n23) => andb (andb (beq_nat n11 n21) (beq_nat n12 n22))
                                            (beq_nat n13 n23)
  end.

(** Maps are defined as functions *)
Definition totalMap (K V : Type) := K -> V.

Definition partialMap (K V : Type) := totalMap K (option V).

Definition tmapEmpty {K V : Type} (v : V) : totalMap K V := (fun _ => v).

Definition emptymap {K V :Type} : partialMap K V := tmapEmpty None.

Definition tUpdate {K V : Type} (beq : K -> K -> bool) (m : totalMap K V) (k : K) (v : V) :=
  fun k' => if beq k k' then v else m k'.

Definition update {K V : Type} (beq : K -> K -> bool) (m : partialMap K V) (k : K) (v : V) :=
  tUpdate beq m k (Some v).

Definition Memo := partialMap ID Decision.

Definition ListMemo := partialMap ID unit.

(* Collect values of a choice tree while respecting shared decisions. *)
Fixpoint dfs A (m : Memo) (t : Tree A) : list A :=
  match t with
  | Empty _ => Datatypes.nil
  | Leaf x => Datatypes.cons x Datatypes.nil
  | Branch None l r => app (dfs m l) (dfs m r)
  | Branch (Some id) l r => match m id with
                           | None => app (dfs (update beqId m id L) l)
                                        (dfs (update beqId m id R) r)
                           | Some L => dfs m l
                           | Some R => dfs m r
                           end
  end.

Definition collectVals A := @dfs A emptymap.

(* Filter out duplicate messages from a list of messages with sharing IDs. *)
Fixpoint compute_log (m : ListMemo) (xs : list (option ID * string)) : list string :=
  match xs with
  | nil                    => nil
  | cons (None, msg)    ys => cons msg (compute_log m ys)
  | cons (Some id, msg) ys => match m id with
     | None   => cons msg (compute_log (update beqId m id tt) ys)
     | Some _ => compute_log m ys
     end
  end.

Definition collectMessages (A : Type) (x : (A * list (option ID * string))) : (A * list string) :=
   (fst x,compute_log emptymap (snd x)).

Definition discardMessages (A : Type) (x : (A * list (option ID * string))) : A :=
   fst x.
