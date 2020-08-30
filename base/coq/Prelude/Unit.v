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

  (* smart constructor *)
  Definition Tt : Free' Unit' := pure tt.

End SecUnit.

(* Normalform instance for Unit *)

Instance NormalformUnit (Shape : Type) (Pos : Shape -> Type)
  : Normalform Shape Pos (Unit Shape Pos) (Unit Identity.Shape Identity.Pos)
  := { nf' := pure }.

(* ShareableArgs instance for Unit *)

Instance ShareableArgsUnit (Shape : Type) (Pos : Shape -> Type)
  : ShareableArgs Shape Pos (Unit Shape Pos)
 := {
        shareArgs := pure
    }.