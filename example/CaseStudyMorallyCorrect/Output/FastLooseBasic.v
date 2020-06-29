(* module FastLooseBasic *)

From Base Require Import Free.

From Base Require Import Prelude.

From Base Require Import Test.QuickCheck.

(* Data type declarations for Peano *)

Inductive Peano (Shape : Type) (Pos : Shape -> Type) : Type
  := zero : Peano Shape Pos
  |  s : Free Shape Pos (Peano Shape Pos) -> Peano Shape Pos.

(* Arguments sentences for Peano *)

Arguments zero {Shape} {Pos}.

Arguments s {Shape} {Pos}.

(* Smart constructors for Peano *)

Definition Zero (Shape : Type) (Pos : Shape -> Type)
   : Free Shape Pos (Peano Shape Pos) :=
  pure zero.

Definition S (Shape : Type) (Pos : Shape -> Type) (x_0
    : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos (Peano Shape Pos) :=
  pure (s x_0).

(* Helper functions for rev *)

Fixpoint rev_0 (Shape : Type) (Pos : Shape -> Type) {t0 : Type} (a11
                 : List Shape Pos t0) (a12 : Free Shape Pos (List Shape Pos t0)) {struct a11}
           : Free Shape Pos (List Shape Pos t0)
           := match a11 with
              | nil => a12
              | cons a13 a14 =>
                  a14 >>=
                  (fun (a14_0 : List Shape Pos t0) =>
                     @rev_0 Shape Pos t0 a14_0 (@Cons Shape Pos t0 a13 a12))
              end.

Definition rev (Shape : Type) (Pos : Shape -> Type) {t0 : Type} (a11
    : Free Shape Pos (List Shape Pos t0)) (a12
    : Free Shape Pos (List Shape Pos t0))
   : Free Shape Pos (List Shape Pos t0) :=
  a11 >>= (fun (a11_0 : List Shape Pos t0) => @rev_0 Shape Pos t0 a11_0 a12).

Definition reverse (Shape : Type) (Pos : Shape -> Type) {a : Type} (xs
    : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (List Shape Pos a) :=
  @rev Shape Pos a xs (@Nil Shape Pos a).

Definition prop_rev_is_rev_inv (Shape : Type) (Pos : Shape -> Type) {a : Type}
  (xs : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (List Shape Pos a) (@reverse Shape Pos a (@reverse Shape Pos a
                                                              xs)) xs.

Definition pred (Shape : Type) (Pos : Shape -> Type) (a23
    : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos (Peano Shape Pos) :=
  a23 >>=
  (fun a23_0 => match a23_0 with | zero => Zero Shape Pos | s a24 => a24 end).

Section section_map_0.
(* Constant arguments for map *)
Variable Shape : Type.
Variable Pos : Shape -> Type.
Variable a_0 b_0 : Type.
Variable a17_0 : Free Shape Pos (Free Shape Pos a_0 -> Free Shape Pos b_0).
(* Helper functions for map *)
Fixpoint map_1 (a18 : List Shape Pos a_0) {struct a18} : Free Shape Pos (List
                                                               Shape Pos b_0)
           := match a18 with
              | nil => @Nil Shape Pos b_0
              | cons a19 a20 =>
                  @Cons Shape Pos b_0 (a17_0 >>= (fun a17_1 => a17_1 a19)) (a20 >>=
                                       (fun (a20_0 : List Shape Pos a_0) => map_1 a20_0))
              end.
(* Main functions for map *)
Definition map_0 (a18 : Free Shape Pos (List Shape Pos a_0))
   : Free Shape Pos (List Shape Pos b_0) :=
  a18 >>= (fun (a18_0 : List Shape Pos a_0) => map_1 a18_0).
End section_map_0.

Definition map (Shape : Type) (Pos : Shape -> Type) {a b : Type} (a17
    : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b)) (a18
    : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (List Shape Pos b) :=
  map_0 Shape Pos a b a17 a18.

Definition id (Shape : Type) (Pos : Shape -> Type) {a : Type} (a0
    : Free Shape Pos a)
   : Free Shape Pos a :=
  a0.

Section section_foldPeano_0.
(* Constant arguments for foldPeano *)
Variable Shape : Type.
Variable Pos : Shape -> Type.
Variable a_0 : Type.
Variable a27_0 : Free Shape Pos a_0.
Variable a26_0 : Free Shape Pos (Free Shape Pos a_0 -> Free Shape Pos a_0).
(* Helper functions for foldPeano *)
Fixpoint foldPeano_1 (a28 : Peano Shape Pos) {struct a28} : Free Shape Pos a_0
           := match a28 with
              | zero => a27_0
              | s a29 =>
                  a26_0 >>=
                  (fun a26_1 =>
                     a26_1 (a29 >>= (fun (a29_0 : Peano Shape Pos) => foldPeano_1 a29_0)))
              end.
(* Main functions for foldPeano *)
Definition foldPeano_0 (a28 : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos a_0 :=
  a28 >>= (fun (a28_0 : Peano Shape Pos) => foldPeano_1 a28_0).
End section_foldPeano_0.

Definition foldPeano (Shape : Type) (Pos : Shape -> Type) {a : Type} (a26
    : Free Shape Pos (Free Shape Pos a -> Free Shape Pos a)) (a27
    : Free Shape Pos a) (a28 : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos a :=
  foldPeano_0 Shape Pos a a27 a26 a28.

Definition minus (Shape : Type) (Pos : Shape -> Type) (x_0
    : Free Shape Pos (Peano Shape Pos)) (x_1 : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos (Peano Shape Pos) :=
  @foldPeano Shape Pos (Peano Shape Pos) (pure (fun x_2 => pred Shape Pos x_2))
                                         x_0 x_1.

Definition plus (Shape : Type) (Pos : Shape -> Type) (x_0
    : Free Shape Pos (Peano Shape Pos)) (x_1 : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos (Peano Shape Pos) :=
  @foldPeano Shape Pos (Peano Shape Pos) (pure (fun x_2 => S Shape Pos x_2)) x_0
                                         x_1.

Definition prop_minus_is_plus_inv (Shape : Type) (Pos : Shape -> Type) (x
    : Free Shape Pos (Peano Shape Pos)) (y : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (Peano Shape Pos) (minus Shape Pos (plus Shape Pos y x) y) x.

Definition comp (Shape : Type) (Pos : Shape -> Type) {b c a : Type} (g
    : Free Shape Pos (Free Shape Pos b -> Free Shape Pos c)) (f
    : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b)) (a0
    : Free Shape Pos a)
   : Free Shape Pos c :=
  g >>= (fun g_0 => g_0 (f >>= (fun f_0 => f_0 a0))).

Section section_append_0.
(* Constant arguments for append *)
Variable Shape : Type.
Variable Pos : Shape -> Type.
Variable a_0 : Type.
Variable a1_0 : Free Shape Pos (List Shape Pos a_0).
(* Helper functions for append *)
Fixpoint append_1 (a0 : List Shape Pos a_0) {struct a0} : Free Shape Pos (List
                                                                Shape Pos a_0)
           := match a0 with
              | nil => a1_0
              | cons a2 a3 =>
                  @Cons Shape Pos a_0 a2 (a3 >>=
                                       (fun (a3_0 : List Shape Pos a_0) => append_1 a3_0))
              end.
(* Main functions for append *)
Definition append_0 (a0 : Free Shape Pos (List Shape Pos a_0))
   : Free Shape Pos (List Shape Pos a_0) :=
  a0 >>= (fun (a0_0 : List Shape Pos a_0) => append_1 a0_0).
End section_append_0.

Definition append (Shape : Type) (Pos : Shape -> Type) {a : Type} (a0
    : Free Shape Pos (List Shape Pos a)) (a1 : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (List Shape Pos a) :=
  append_0 Shape Pos a a1 a0.

(* Helper functions for reverseNaive *)

Fixpoint reverseNaive_0 (Shape : Type) (Pos : Shape -> Type) {a : Type} (a6
                          : List Shape Pos a) {struct a6} : Free Shape Pos (List Shape Pos a)
           := match a6 with
              | nil => @Nil Shape Pos a
              | cons a7 a8 =>
                  @append Shape Pos a (a8 >>=
                                       (fun (a8_0 : List Shape Pos a) => @reverseNaive_0 Shape Pos a a8_0)) (@Cons
                                       Shape Pos a a7 (@Nil Shape Pos a))
              end.

Definition reverseNaive (Shape : Type) (Pos : Shape -> Type) {a : Type} (a6
    : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (List Shape Pos a) :=
  a6 >>= (fun (a6_0 : List Shape Pos a) => @reverseNaive_0 Shape Pos a a6_0).

Definition prop_reverse_is_reverseNaive (Shape : Type) (Pos : Shape -> Type) {a
   : Type} (xs : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (List Shape Pos a) (@reverse Shape Pos a xs) (@reverseNaive
                                        Shape Pos a xs).
