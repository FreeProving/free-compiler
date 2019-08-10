From Base Require Import Free.
From Base Require Import Prelude.Bool.

(* We need to export this library (instead of just importing it) such that we
   can use the `%Z` suffix in the compiled modules. *)
Require Export ZArith.

(* We define [Int] outside of the section even though we want [Int] to take
   [Shape] and [Pos] as arguments because Coq will only add [Variable]s that 
   are actually used on the right hand side. 
   The reason for us to add the parameters in the first place is that we want
   to unify the translation of build-in and user defined data types. *)
Definition Int (Shape : Type) (Pos : Shape -> Type) : Type := Z.
  
Section SecInt.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).
  Notation "'Int''" := (Int Shape Pos).
  Notation "'Bool''" := (Bool Shape Pos).

  (** * Unary operators *)

  (* unary minus *)
  Definition negate (n : Free' Int') : Free' Int' :=
    n >>= fun(n' : Int') => pure (Z.opp n').

  (** * Binary operators *)

  (* addition *)
  Definition addInt (n1 : Free' Int') (n2 : Free' Int') : Free' Int' :=
    n1 >>= fun(n1' : Int') =>
      n2 >>= fun(n2' : Int') =>
        pure (Z.add n1' n2').

  (* subtraction *)
  Definition subInt (n1 : Free' Int') (n2 : Free' Int') : Free' Int' :=
    n1 >>= fun(n1' : Int') =>
      n2 >>= fun(n2' : Int') =>
        pure (Z.sub n1' n2').

  (* multiplication *)
  Definition mulInt (n1 : Free' Int') (n2 : Free' Int') : Free' Int' :=
    n1 >>= fun(n1' : Int') =>
      n2 >>= fun(n2' : Int') =>
        pure (Z.mul n1' n2').

  (* exponentiation *)
  Definition powInt (n1 : Free' Int') (n2 : Free' Int') : Free' Int' :=
    n1 >>= fun(n1' : Int') =>
      n2 >>= fun(n2' : Int') =>
        pure (Z.pow n1' n2').

  (** * Comparision operators *)

  (* less than or equal *)
  Definition leInt (n1 : Free' Int') (n2 : Free' Int') : Free' Bool' :=
    n1 >>= fun(n1' : Int') =>
      n2 >>= fun(n2' : Int') =>
        pure (Z.leb n1' n2').

  (* less than *)
  Definition ltInt (n1 : Free' Int') (n2 : Free' Int') : Free' Bool' :=
    n1 >>= fun(n1' : Int') =>
      n2 >>= fun(n2' : Int') =>
        pure (Z.ltb n1' n2').

  (* greater than or equal *)
  Definition eqInt (n1 : Free' Int') (n2 : Free' Int') : Free' Bool' :=
    n1 >>= fun(n1' : Int') =>
      n2 >>= fun(n2' : Int') =>
        pure (Z.eqb n1' n2').

  (* greater than *)
  Definition neqInt (n1 : Free' Int') (n2 : Free' Int') : Free' Bool' :=
    n1 >>= fun(n1' : Int') =>
      n2 >>= fun(n2' : Int') =>
        pure (negb (Z.eqb n1' n2')).

  (* greater than or equal *)
  Definition geInt (n1 : Free' Int') (n2 : Free' Int') : Free' Bool' :=
    n1 >>= fun(n1' : Int') =>
      n2 >>= fun(n2' : Int') =>
        pure (Z.geb n1' n2').

  (* greater than *)
  Definition gtInt (n1 : Free' Int') (n2 : Free' Int') : Free' Bool' :=
    n1 >>= fun(n1' : Int') =>
      n2 >>= fun(n2' : Int') =>
        pure (Z.gtb n1' n2').

End SecInt.
