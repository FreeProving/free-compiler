From Base Require Import Free.

(* smart constructors *)
Definition True_
  {F : Type -> Type} {C__F : Container F}
  : Free C__F bool :=
  pure true.
Definition False_
  {F : Type -> Type} {C__F : Container F}
  : Free C__F bool :=
  pure false.

(* conjunction *)
Definition andBool
  {F : Type -> Type} (C__F : Container F)
  (b1 : Free C__F bool) (b2 : Free C__F bool) : Free C__F bool :=
  b1 >>= fun(b1' : bool) =>
    b2 >>= fun(b2' : bool) =>
      pure (andb b1' b2').

(* disjunction *)
Definition orBool
  {F : Type -> Type} (C__F : Container F)
  (b1 : Free C__F bool) (b2 : Free C__F bool) : Free C__F bool :=
  b1 >>= fun(b1' : bool) =>
    b2 >>= fun(b2' : bool) =>
      pure (orb b1' b2').
