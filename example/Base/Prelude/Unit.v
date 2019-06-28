From Base Require Import Free.

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

(* The arguments of the smart constructor are implicit. *)
Arguments Tt {Shape} {Pos}.
