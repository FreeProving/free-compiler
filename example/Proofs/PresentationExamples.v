From Base Require Import Free Handlers.
From Base Require Import Free.Instance.Trace.
From Base Require Import Free.Instance.Maybe.
From Base Require Import Free.Instance.Comb.
From Base Require Import Prelude.
From Base Require Import Test.QuickCheck.
From Generated Require Import Data.List.

Require Import Coq.Logic.FunctionalExtensionality.
Open Scope Z.

(* let x = 1 in x + x =/= 1 + 1 *)
Definition one_plus_one (Shape : Type) (Pos : Shape -> Type) `{Injectable Share.Shape Share.Pos Shape Pos}
:= @neqProp Shape Pos _ _ 
      (@share Shape Pos (Cbneed Shape Pos) _ _ (pure 1) >>= fun x => 
          (addInteger Shape Pos x x)) 
      (addInteger Shape Pos (pure 1) (pure 1)).

Lemma one_plus_one_lemma : quickCheck one_plus_one.
Proof. simpl. intros Shape Pos I. discriminate. Qed.

Definition S := Share.Shape.
Definition P := Share.Pos.
Definition one_plus_two 
:= @neqProp S P _ _
      (@share S P (Cbneed S P) _ _ (pure 1) >>= fun x => 
          (@share S P (Cbneed S P) _ _ (pure 2) >>= fun y => 
              (addInteger S P x y)))
      (@share S P (Cbneed S P) _ _ (pure 2) >>= fun y => 
          (@share S P (Cbneed S P) _ _ (pure 1) >>= fun x => 
              (addInteger S P x y))).
Lemma one_plus_two_lemma : quickCheck one_plus_two.
Proof. simpl. unfold addInteger. simpl. Admitted.







































(* Handler strictness *)

(* [undefined] *)
Definition undefList (Shape : Type) (Pos : Shape -> Type)
                (P : Partial Shape Pos)
  : Free Shape Pos (List Shape Pos (Unit Shape Pos))
 := Cons Shape Pos undefined (Nil Shape Pos).

(* undefined *)
Definition undef (Shape : Type) (Pos : Shape -> Type)
                (P : Partial Shape Pos)
  : Free Shape Pos (List Shape Pos (Unit Shape Pos))
 := undefined.

Definition SMaybe := Comb.Shape Maybe.Shape Identity.Shape.
Definition PMaybe := Comb.Pos Maybe.Pos Identity.Pos.

(* [undefined] != undefined in a partial setting. *)
Lemma undefList_neq_undef : 
  undefList SMaybe PMaybe (Maybe.Partial SMaybe PMaybe) 
  <> 
  undef SMaybe PMaybe (Maybe.Partial SMaybe PMaybe).
Proof. discriminate. Qed.

(* For completeness' sake: length [undefined] != length undefined. *)
Lemma length_undefList_neq_length_ex2 : 
  length SMaybe PMaybe (undefList SMaybe PMaybe (Maybe.Partial SMaybe PMaybe))
  <>
  length SMaybe PMaybe (undef SMaybe PMaybe (Maybe.Partial SMaybe PMaybe)).
Proof. discriminate. Qed.

(* handle [undefined] = handle undefined in the same setting
   using the appropriate handler. *)
Lemma handle_undefList_eq_handle_undef :
  @handle SMaybe PMaybe _ (HandlerMaybe _)
    (undefList SMaybe PMaybe (Maybe.Partial SMaybe PMaybe))
  = 
  @handle SMaybe PMaybe _ (HandlerMaybe _) 
    (undef SMaybe PMaybe (Maybe.Partial SMaybe PMaybe)).
Proof.
(* Equation is reduced to None = None *)
simpl. reflexivity. Qed.

(* But handle (length [undefined]) != handle (length undefined) using
   the same setting and handler. *)
Lemma length_handle_undefList_new_length_handle_ex2 :
  @handle SMaybe PMaybe _ (HandlerMaybe _)
    (length SMaybe PMaybe (undefList SMaybe PMaybe (Maybe.Partial SMaybe PMaybe)))
  <>
  @handle SMaybe PMaybe _ (HandlerMaybe _)
    (length SMaybe PMaybe (undef SMaybe PMaybe (Maybe.Partial SMaybe PMaybe))).
(* Equation is reduced to Some 1 <> None. *)
Proof. simpl. discriminate. Qed.