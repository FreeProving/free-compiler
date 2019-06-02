From Base Require Import Free.

(* We need to export this library (instead of just importing it) such that we
   can use the `%Z` suffix in the compiled modules. *)
Require Export ZArith.

Definition Int : Type := Z.

(** * Unary operators *)

(* unary minus *)
Definition negate
  {F : Type -> Type} (C__F : Container F)
  (n : Free C__F Int) : Free C__F Int :=
  n >>= fun(n' : Int) => pure (Z.opp n').

(** * Binary operators *)

(* addition *)
Definition addInt
  {F : Type -> Type} (C__F : Container F)
  (n1 : Free C__F Int) (n2 : Free C__F Int) : Free C__F Int :=
  n1 >>= fun(n1' : Int) =>
    n2 >>= fun(n2' : Int) =>
      pure (Z.add n1' n2').

(* subtraction *)
Definition subInt
  {F : Type -> Type} (C__F : Container F)
  (n1 : Free C__F Int) (n2 : Free C__F Int) : Free C__F Int :=
  n1 >>= fun(n1' : Int) =>
    n2 >>= fun(n2' : Int) =>
      pure (Z.sub n1' n2').

(* multiplication *)
Definition mulInt
  {F : Type -> Type} (C__F : Container F)
  (n1 : Free C__F Int) (n2 : Free C__F Int) : Free C__F Int :=
  n1 >>= fun(n1' : Int) =>
    n2 >>= fun(n2' : Int) =>
      pure (Z.mul n1' n2').

(* exponentiation *)
Definition powInt
  {F : Type -> Type} (C__F : Container F)
  (n1 : Free C__F Int) (n2 : Free C__F Int) : Free C__F Int :=
  n1 >>= fun(n1' : Int) =>
    n2 >>= fun(n2' : Int) =>
      pure (Z.pow n1' n2').

(** * Comparision operators *)

(* less than or equal *)
Definition leInt
  {F : Type -> Type} (C__F : Container F)
  (n1 : Free C__F Int) (n2 : Free C__F Int) : Free C__F bool :=
  n1 >>= fun(n1' : Int) =>
    n2 >>= fun(n2' : Int) =>
      pure (Z.leb n1' n2').

(* less than *)
Definition ltInt
  {F : Type -> Type} (C__F : Container F)
  (n1 : Free C__F Int) (n2 : Free C__F Int) : Free C__F bool :=
  n1 >>= fun(n1' : Int) =>
    n2 >>= fun(n2' : Int) =>
      pure (Z.ltb n1' n2').

(* greater than or equal *)
Definition eqInt
  {F : Type -> Type} (C__F : Container F)
  (n1 : Free C__F Int) (n2 : Free C__F Int) : Free C__F bool :=
  n1 >>= fun(n1' : Int) =>
    n2 >>= fun(n2' : Int) =>
      pure (Z.eqb n1' n2').

(* greater than *)
Definition neqInt
  {F : Type -> Type} (C__F : Container F)
  (n1 : Free C__F Int) (n2 : Free C__F Int) : Free C__F bool :=
  n1 >>= fun(n1' : Int) =>
    n2 >>= fun(n2' : Int) =>
      pure (negb (Z.eqb n1' n2')).

(* greater than or equal *)
Definition geInt
  {F : Type -> Type} (C__F : Container F)
  (n1 : Free C__F Int) (n2 : Free C__F Int) : Free C__F bool :=
  n1 >>= fun(n1' : Int) =>
    n2 >>= fun(n2' : Int) =>
      pure (Z.geb n1' n2').

(* greater than *)
Definition gtInt
  {F : Type -> Type} (C__F : Container F)
  (n1 : Free C__F Int) (n2 : Free C__F Int) : Free C__F bool :=
  n1 >>= fun(n1' : Int) =>
    n2 >>= fun(n2' : Int) =>
      pure (Z.gtb n1' n2').
