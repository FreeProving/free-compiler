(** * Collection of definitions used by the tests. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Instance.Trace.
From Base Require Import Prelude.
From Base Require Import Free.Util.Search.

Section SecUtilFunc.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).
  Notation "'Pair''" := (Pair Shape Pos).
  Notation "'List''" := (List Shape Pos).

  (* First element of a pair *)
  Definition fstPair {A B : Type} (fp : Free' (Pair' A B))
   : Free Shape Pos A
  := fp >>= fun p => match p with
                    | pair_ x _ => x
                    end.

  (* Second element of a pair *)
  Definition sndPair {A B : Type} (fp : Free' (Pair' A B))
   : Free Shape Pos B
  := fp >>= fun p => match p with
                    | pair_ _ y => y
                    end.

  (* Partially defined head of a list *)
  Definition headList {A : Type} (P : Partial Shape Pos) (fl : Free' (List' A))
   : Free Shape Pos A
  := fl >>= fun l => match l with
                     | List.cons fx _ => fx
                     | List.nil       => @undefined Shape Pos P A
                     end.

End SecUtilFunc.
