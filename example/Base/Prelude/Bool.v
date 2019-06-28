From Base Require Import Free.

(* We define an alias for [bool] that accepts the parameters [Shape] and
   [Pos] to unify the translation of build-in and user defined data types.
   We cannot define [Bool] in the section below, because Coq won't add
   [Variable]s to definitions that don't use them. *)
Definition Bool (Shape : Type) (Pos : Shape -> Type) : Type := bool.

Section SecBool.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).
  Notation "'Bool''" := (Bool Shape Pos).

  (* smart constructors *)
  Definition True_ : Free' Bool' := pure true.
  Definition False_ : Free' Bool' := pure false.

  (* conjunction *)
  Definition andBool (b1 : Free' Bool') (b2 : Free' Bool') : Free' Bool' :=
    b1 >>= fun(b1' : Bool') =>
      b2 >>= fun(b2' : Bool') =>
        pure (andb b1' b2').

  (* disjunction *)
  Definition orBool (b1 : Free' Bool') (b2 : Free' Bool') : Free' Bool' :=
    b1 >>= fun(b1' : Bool') =>
      b2 >>= fun(b2' : Bool') =>
        pure (orb b1' b2').

End SecBool.

(* The arguments of the smart constructors are implicit. *)
Arguments True_  {Shape} {Pos}.
Arguments False_ {Shape} {Pos}.
