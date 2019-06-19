From Base Require Import Free.

(* We need to export this library (instead of just importing it) such that we
   can use the `%Z` suffix in the compiled modules. *)
Require Export ZArith.

(* We define [Int] outside of the section below, because in contrast to build 
   in data types like [List] and [Pair] we don't want to pass [Shape] and [Pos] 
   to primitive data types like [Int], [bool] and [unit]. *)
Definition Int : Type := Z.

Section SecInt.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).

  (** * Unary operators *)

  (* unary minus *)
  Definition negate (n : Free' Int) : Free' Int :=
    n >>= fun(n' : Int) => pure (Z.opp n').

  (** * Binary operators *)

  (* addition *)
  Definition addInt (n1 : Free' Int) (n2 : Free' Int) : Free' Int :=
    n1 >>= fun(n1' : Int) =>
      n2 >>= fun(n2' : Int) =>
        pure (Z.add n1' n2').

  (* subtraction *)
  Definition subInt (n1 : Free' Int) (n2 : Free' Int) : Free' Int :=
    n1 >>= fun(n1' : Int) =>
      n2 >>= fun(n2' : Int) =>
        pure (Z.sub n1' n2').

  (* multiplication *)
  Definition mulInt (n1 : Free' Int) (n2 : Free' Int) : Free' Int :=
    n1 >>= fun(n1' : Int) =>
      n2 >>= fun(n2' : Int) =>
        pure (Z.mul n1' n2').

  (* exponentiation *)
  Definition powInt (n1 : Free' Int) (n2 : Free' Int) : Free' Int :=
    n1 >>= fun(n1' : Int) =>
      n2 >>= fun(n2' : Int) =>
        pure (Z.pow n1' n2').

  (** * Comparision operators *)

  (* less than or equal *)
  Definition leInt (n1 : Free' Int) (n2 : Free' Int) : Free' bool :=
    n1 >>= fun(n1' : Int) =>
      n2 >>= fun(n2' : Int) =>
        pure (Z.leb n1' n2').

  (* less than *)
  Definition ltInt (n1 : Free' Int) (n2 : Free' Int) : Free' bool :=
    n1 >>= fun(n1' : Int) =>
      n2 >>= fun(n2' : Int) =>
        pure (Z.ltb n1' n2').

  (* greater than or equal *)
  Definition eqInt (n1 : Free' Int) (n2 : Free' Int) : Free' bool :=
    n1 >>= fun(n1' : Int) =>
      n2 >>= fun(n2' : Int) =>
        pure (Z.eqb n1' n2').

  (* greater than *)
  Definition neqInt (n1 : Free' Int) (n2 : Free' Int) : Free' bool :=
    n1 >>= fun(n1' : Int) =>
      n2 >>= fun(n2' : Int) =>
        pure (negb (Z.eqb n1' n2')).

  (* greater than or equal *)
  Definition geInt (n1 : Free' Int) (n2 : Free' Int) : Free' bool :=
    n1 >>= fun(n1' : Int) =>
      n2 >>= fun(n2' : Int) =>
        pure (Z.geb n1' n2').

  (* greater than *)
  Definition gtInt (n1 : Free' Int) (n2 : Free' Int) : Free' bool :=
    n1 >>= fun(n1' : Int) =>
      n2 >>= fun(n2' : Int) =>
        pure (Z.gtb n1' n2').

End SecInt.