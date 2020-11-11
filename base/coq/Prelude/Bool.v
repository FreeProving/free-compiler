From Base Require Import Free.
From Base Require Import Free.Instance.Identity.

(* We define an alias for [bool] that accepts the parameters [Shape] and
   [Pos] to unify the translation of build-in and user defined data types.
   We cannot define [Bool] in the section below, because Coq won't add
   [Variable]s to definitions that don't use them. *)
Definition Bool (Shape : Type) (Pos : Shape -> Type) : Type := bool.

(* smart constructors *)

Notation "'True_' Shape Pos" := (@pure Shape Pos bool true)
  ( at level 10, Shape, Pos at level 9 ).

Notation "'@True_' Shape Pos" := (@pure Shape Pos bool true)
  ( only parsing, at level 10, Shape, Pos at level 9 ).

Notation "'False_' Shape Pos" := (@pure Shape Pos bool false)
  ( at level 10, Shape, Pos at level 9 ).

Notation "'@False_' Shape Pos" := (@pure Shape Pos bool false)
  ( only parsing, at level 10, Shape, Pos at level 9 ).

Section SecBool.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).
  Notation "'Bool''" := (Bool Shape Pos).

  (* conjunction *)
  Definition andBool (b1 : Free' Bool') (b2 : Free' Bool') : Free' Bool' :=
    b1 >>= fun(b1' : Bool') => if b1' then b2 else False_ Shape Pos.

  (* disjunction *)
  Definition orBool (b1 : Free' Bool') (b2 : Free' Bool') : Free' Bool' :=
    b1 >>= fun(b1' : Bool') => if b1' then True_ Shape Pos else b2.

  (* helper function for guards *)
  Definition otherwise : Free' Bool' := True_ Shape Pos.

End SecBool.

(* Normalform instance for Bool *)

Instance NormalformBool (Shape : Type) (Pos : Shape -> Type)
  : Normalform Shape Pos (Bool Shape Pos)
  := { nf' := pure }.

(* ShareableArgs instance for Bool *)

Instance ShareableArgsBool (Shape : Type) (Pos : Shape -> Type)
  : ShareableArgs Shape Pos (Bool Shape Pos)
 := { shareArgs _ := pure }.
