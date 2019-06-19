From Base Require Import Free.

Section SecUnit.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).

  (* smart constructor *)
  Definition Tt : Free' unit := pure tt.

End SecUnit.

(* The arguments of the smart constructor are implicit. *)
Arguments Tt {Shape} {Pos}.