From Base Require Import Free.
From Base Require Import Free.Instance.Identity.

(* We define an alias for [unit] that accepts the parameters [Shape] and
   [Pos] to unify the translation of build-in and user defined data types.
   We cannot define [Unit] in the section below, because Coq won't add
   [Variable]s to definitions that don't use them. *)
Definition Unit (Shape : Type) (Pos : Shape -> Type) : Type := unit.

Section SecUnit.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).
  Notation "'Unit''" := (Unit Shape Pos).

End SecUnit.

(* smart constructor *)

Notation "'Tt' Shape Pos" := (@pure Shape Pos unit tt)
  ( at level 10, Shape, Pos at level 9 ).

Notation "'@Tt' Shape Pos" := (@pure Shape Pos unit tt)
  ( only parsing, at level 10, Shape, Pos at level 9 ).

(* Normalform instance for Unit *)

Instance NormalformUnit (Shape : Type) (Pos : Shape -> Type)
  : Normalform Shape Pos (Unit Shape Pos)
  := { nf' := pure }.

(* ShareableArgs instance for Unit *)

Instance ShareableArgsUnit (Shape : Type) (Pos : Shape -> Type)
  : ShareableArgs Shape Pos (Unit Shape Pos)
 := { shareArgs _ := pure }.
