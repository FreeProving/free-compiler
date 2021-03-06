From Base Require Import Free.
From Base Require Import Free.Instance.Identity.
From Base Require Import Prelude.Bool.

(* We need to export this library (instead of just importing it) such that we
   can use the `%Z` suffix in the compiled modules. *)
Require Export ZArith.

(* We define [Integer] outside of the section even though we want [Integer] to
   take [Shape] and [Pos] as arguments because Coq will only add [Variable]s
   that are actually used on the right hand side.
   The reason for us to add the parameters in the first place is that we want
   to unify the translation of build-in and user defined data types. *)
Definition Integer (Shape : Type) (Pos : Shape -> Type) : Type := Z.

Section SecInteger.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).
  Notation "'Integer''" := (Integer Shape Pos).
  Notation "'Bool''" := (Bool Shape Pos).

  (** * Unary operators *)

  (* unary minus *)
  Definition negate (n : Free' Integer') : Free' Integer' :=
    n >>= fun(n' : Integer') => pure (Z.opp n').

  (** * Binary operators *)

  (* addition *)
  Definition addInteger (n1 : Free' Integer') (n2 : Free' Integer') : Free' Integer' :=
    n1 >>= fun(n1' : Integer') =>
      n2 >>= fun(n2' : Integer') =>
        pure (Z.add n1' n2').

  (* subtraction *)
  Definition subInteger (n1 : Free' Integer') (n2 : Free' Integer') : Free' Integer' :=
    n1 >>= fun(n1' : Integer') =>
      n2 >>= fun(n2' : Integer') =>
        pure (Z.sub n1' n2').

  (* multiplication *)
  Definition mulInteger (n1 : Free' Integer') (n2 : Free' Integer') : Free' Integer' :=
    n1 >>= fun(n1' : Integer') =>
      n2 >>= fun(n2' : Integer') =>
        pure (Z.mul n1' n2').

  (* exponentiation *)
  Definition powInteger (P : Partial Shape Pos) (n1 : Free' Integer') (n2 : Free' Integer') : Free' Integer' :=
    n2 >>= fun(n2' : Integer') =>
      if Z.ltb n2' 0
        then error "Negative exponent"
        else if Z.eqb n2' 0
               then pure 1%Z
               else n1 >>= fun(n1' : Integer') =>
                 pure (Z.pow n1' n2').

  (** * Comparison operators *)

  (* less than or equal *)
  Definition leInteger (n1 : Free' Integer') (n2 : Free' Integer') : Free' Bool' :=
    n1 >>= fun(n1' : Integer') =>
      n2 >>= fun(n2' : Integer') =>
        pure (Z.leb n1' n2').

  (* less than *)
  Definition ltInteger (n1 : Free' Integer') (n2 : Free' Integer') : Free' Bool' :=
    n1 >>= fun(n1' : Integer') =>
      n2 >>= fun(n2' : Integer') =>
        pure (Z.ltb n1' n2').

  (* greater than or equal *)
  Definition eqInteger (n1 : Free' Integer') (n2 : Free' Integer') : Free' Bool' :=
    n1 >>= fun(n1' : Integer') =>
      n2 >>= fun(n2' : Integer') =>
        pure (Z.eqb n1' n2').

  (* greater than *)
  Definition neqInteger (n1 : Free' Integer') (n2 : Free' Integer') : Free' Bool' :=
    n1 >>= fun(n1' : Integer') =>
      n2 >>= fun(n2' : Integer') =>
        pure (negb (Z.eqb n1' n2')).

  (* greater than or equal *)
  Definition geInteger (n1 : Free' Integer') (n2 : Free' Integer') : Free' Bool' :=
    n1 >>= fun(n1' : Integer') =>
      n2 >>= fun(n2' : Integer') =>
        pure (Z.geb n1' n2').

  (* greater than *)
  Definition gtInteger (n1 : Free' Integer') (n2 : Free' Integer') : Free' Bool' :=
    n1 >>= fun(n1' : Integer') =>
      n2 >>= fun(n2' : Integer') =>
        pure (Z.gtb n1' n2').

End SecInteger.

(* Normalform instance for Integer *)

Instance NormalformInteger (Shape : Type) (Pos : Shape -> Type)
  : Normalform Shape Pos (Integer Shape Pos)
  := { nf' := pure }.

(* ShareableArgs instance for Integer *)

Instance ShareableArgsInteger (Shape : Type) (Pos : Shape -> Type)
  : ShareableArgs Shape Pos (Integer Shape Pos)
 := { shareArgs _ := pure }.
