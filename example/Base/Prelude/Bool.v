From Base Require Import Free.

Section SecBool.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).

  (* smart constructors *)
  Definition True_ : Free' bool := pure true.
  Definition False_ : Free' bool := pure false.

  (* conjunction *)
  Definition andBool (b1 : Free' bool) (b2 : Free' bool) : Free' bool :=
    b1 >>= fun(b1' : bool) =>
      b2 >>= fun(b2' : bool) =>
        pure (andb b1' b2').

  (* disjunction *)
  Definition orBool (b1 : Free' bool) (b2 : Free' bool) : Free' bool :=
    b1 >>= fun(b1' : bool) =>
      b2 >>= fun(b2' : bool) =>
        pure (orb b1' b2').

End SecBool.

(* The arguments of the smart constructors are implicit. *)
Arguments True_  {Shape} {Pos}.
Arguments False_ {Shape} {Pos}.
