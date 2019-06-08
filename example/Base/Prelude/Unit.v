From Base Require Import Free.

(* smart constructor *)
Definition Tt
  {F : Type -> Type} {C__F : Container F}
  : Free C__F unit :=
  pure tt.
