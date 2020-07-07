(** Definition of choice trees and the depth-first search algorithm *)

Require Import EqNat.

Set Implicit Arguments.

Definition ID : Type := nat * nat * nat.

Inductive Tree A :=
| Empty  : Tree A
| Leaf   : A -> Tree A
| Branch : option ID -> Tree A -> Tree A -> Tree A.

Inductive Decision := L | R.

Definition beq_id (id1 id2 : ID) : bool :=
  match id1,id2 with
  | (n11, n12, n13), (n21, n22, n23) => andb (andb (beq_nat n11 n21) (beq_nat n12 n22))
                                            (beq_nat n13 n23)
  end.

(** Maps are defined as functions *)
Definition total_map (K V : Type) := K -> V.

Definition partial_map (K V : Type) := total_map K (option V).

Definition tmap_empty {K V : Type} (v : V) : total_map K V := (fun _ => v).

Definition emptymap {K V :Type} : partial_map K V := tmap_empty None.

Definition t_update {K V : Type} (beq : K -> K -> bool) (m : total_map K V) (k : K) (v : V) :=
  fun k' => if beq k k' then v else m k'.

Definition update {K V : Type} (beq : K -> K -> bool) (m : partial_map K V) (k : K) (v : V) :=
  t_update beq m k (Some v).

Definition Memo := partial_map ID Decision.

Fixpoint dfs A (m : Memo) (t : Tree A) : list A :=
  match t with
  | Empty _ => Datatypes.nil
  | Leaf x => Datatypes.cons x Datatypes.nil
  | Branch None l r => app (dfs m l) (dfs m r)
  | Branch (Some id) l r => match m id with
                           | None => app (dfs (update beq_id m id L) l)
                                        (dfs (update beq_id m id R) r)
                           | Some L => dfs m l
                           | Some R => dfs m r
                           end
  end.

Definition collectVals A := @dfs A emptymap.