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

Fixpoint rev_0 (Shape : Type) (Pos : Shape -> Type) {t0 : Type} (a15
                 : List Shape Pos t0) (a16 : Free Shape Pos (List Shape Pos t0)) {struct a15}
           : Free Shape Pos (List Shape Pos t0)
           := match a15 with
              | nil => a16
              | cons a17 a18 =>
                  a18 >>=
                  (fun (a18_0 : List Shape Pos t0) =>
                     @rev_0 Shape Pos t0 a18_0 (@Cons Shape Pos t0 a17 a16))
              end.

Definition rev (Shape : Type) (Pos : Shape -> Type) {t0 : Type} (a15
    : Free Shape Pos (List Shape Pos t0)) (a16
    : Free Shape Pos (List Shape Pos t0))
   : Free Shape Pos (List Shape Pos t0) :=
  a15 >>= (fun (a15_0 : List Shape Pos t0) => @rev_0 Shape Pos t0 a15_0 a16).

Definition reverse (Shape : Type) (Pos : Shape -> Type) {a : Type} (xs
    : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (List Shape Pos a) :=
  @rev Shape Pos a xs (@Nil Shape Pos a).

Definition prop_rev_is_rev_inv (Shape : Type) (Pos : Shape -> Type) {a : Type}
  (xs : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (List Shape Pos a) (@reverse Shape Pos a (@reverse Shape Pos a
                                                              xs)) xs.

Definition pred (Shape : Type) (Pos : Shape -> Type) (a27
    : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos (Peano Shape Pos) :=
  a27 >>=
  (fun a27_0 => match a27_0 with | zero => Zero Shape Pos | s a28 => a28 end).

Section section_map_0.
(* Constant arguments for map *)
Variable Shape : Type.
Variable Pos : Shape -> Type.
Variable a_0 b_0 : Type.
Variable a21_0 : Free Shape Pos (Free Shape Pos a_0 -> Free Shape Pos b_0).
(* Helper functions for map *)
Fixpoint map_1 (a22 : List Shape Pos a_0) {struct a22} : Free Shape Pos (List
                                                               Shape Pos b_0)
           := match a22 with
              | nil => @Nil Shape Pos b_0
              | cons a23 a24 =>
                  @Cons Shape Pos b_0 (a21_0 >>= (fun a21_1 => a21_1 a23)) (a24 >>=
                                       (fun (a24_0 : List Shape Pos a_0) => map_1 a24_0))
              end.
(* Main functions for map *)
Definition map_0 (a22 : Free Shape Pos (List Shape Pos a_0))
   : Free Shape Pos (List Shape Pos b_0) :=
  a22 >>= (fun (a22_0 : List Shape Pos a_0) => map_1 a22_0).
End section_map_0.

Definition map (Shape : Type) (Pos : Shape -> Type) {a b : Type} (a21
    : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b)) (a22
    : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (List Shape Pos b) :=
  map_0 Shape Pos a b a21 a22.

Definition id (Shape : Type) (Pos : Shape -> Type) {a : Type} (a0
    : Free Shape Pos a)
   : Free Shape Pos a :=
  a0.

Definition prop_map_id (Shape : Type) (Pos : Shape -> Type) {a : Type} (xs
    : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (List Shape Pos a) (@map Shape Pos a a (pure (fun x_0 =>
                                                                    @id Shape Pos a x_0)) xs) xs.

Section section_foldPeano_0.
(* Constant arguments for foldPeano *)
Variable Shape : Type.
Variable Pos : Shape -> Type.
Variable a_0 : Type.
Variable a31_0 : Free Shape Pos a_0.
Variable a30_0 : Free Shape Pos (Free Shape Pos a_0 -> Free Shape Pos a_0).
(* Helper functions for foldPeano *)
Fixpoint foldPeano_1 (a32 : Peano Shape Pos) {struct a32} : Free Shape Pos a_0
           := match a32 with
              | zero => a31_0
              | s a33 =>
                  a30_0 >>=
                  (fun a30_1 =>
                     a30_1 (a33 >>= (fun (a33_0 : Peano Shape Pos) => foldPeano_1 a33_0)))
              end.
(* Main functions for foldPeano *)
Definition foldPeano_0 (a32 : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos a_0 :=
  a32 >>= (fun (a32_0 : Peano Shape Pos) => foldPeano_1 a32_0).
End section_foldPeano_0.

Definition foldPeano (Shape : Type) (Pos : Shape -> Type) {a : Type} (a30
    : Free Shape Pos (Free Shape Pos a -> Free Shape Pos a)) (a31
    : Free Shape Pos a) (a32 : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos a :=
  foldPeano_0 Shape Pos a a31 a30 a32.

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

Definition comp (Shape : Type) (Pos : Shape -> Type) {b c a : Type} (g
    : Free Shape Pos (Free Shape Pos b -> Free Shape Pos c)) (f
    : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b)) (a0
    : Free Shape Pos a)
   : Free Shape Pos c :=
  g >>= (fun g_0 => g_0 (f >>= (fun f_0 => f_0 a0))).

Definition porp_morally_correct (Shape : Type) (Pos : Shape -> Type) (y
    : Free Shape Pos (Peano Shape Pos)) (xs
    : Free Shape Pos (List Shape Pos (Peano Shape Pos)))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (List Shape Pos (Peano Shape Pos)) (@comp Shape Pos (List
                                                         Shape Pos (Peano Shape Pos)) (List Shape Pos (Peano Shape Pos))
                                                        (List Shape Pos (Peano Shape Pos)) (pure (fun x_0 =>
                                                                                                    @comp Shape Pos
                                                                                                    (List Shape Pos
                                                                                                          (Peano Shape
                                                                                                                 Pos))
                                                                                                    (List Shape Pos
                                                                                                          (Peano Shape
                                                                                                                 Pos))
                                                                                                    (List Shape Pos
                                                                                                          (Peano Shape
                                                                                                                 Pos))
                                                                                                    (pure (fun x_1 =>
                                                                                                             @reverse
                                                                                                             Shape Pos
                                                                                                             (Peano
                                                                                                              Shape Pos)
                                                                                                             x_1)) (pure
                                                                                                     (fun x_1 =>
                                                                                                        @map Shape Pos
                                                                                                        (Peano Shape
                                                                                                               Pos)
                                                                                                        (Peano Shape
                                                                                                               Pos)
                                                                                                        (pure (fun (a2
                                                                                                                 : Free
                                                                                                                   Shape
                                                                                                                   Pos
                                                                                                                   (Peano
                                                                                                                    Shape
                                                                                                                    Pos)) =>
                                                                                                                 minus
                                                                                                                 Shape
                                                                                                                 Pos a2
                                                                                                                 y))
                                                                                                        x_1)) x_0))
                                                                                           (pure (fun x_0 =>
                                                                                                    @comp Shape Pos
                                                                                                    (List Shape Pos
                                                                                                          (Peano Shape
                                                                                                                 Pos))
                                                                                                    (List Shape Pos
                                                                                                          (Peano Shape
                                                                                                                 Pos))
                                                                                                    (List Shape Pos
                                                                                                          (Peano Shape
                                                                                                                 Pos))
                                                                                                    (pure (fun x_1 =>
                                                                                                             @map Shape
                                                                                                             Pos (Peano
                                                                                                              Shape Pos)
                                                                                                             (Peano
                                                                                                              Shape Pos)
                                                                                                             (pure
                                                                                                              (fun (a3
                                                                                                                 : Free
                                                                                                                   Shape
                                                                                                                   Pos
                                                                                                                   (Peano
                                                                                                                    Shape
                                                                                                                    Pos)) =>
                                                                                                                 plus
                                                                                                                 Shape
                                                                                                                 Pos y
                                                                                                                 a3))
                                                                                                             x_1)) (pure
                                                                                                     (fun x_1 =>
                                                                                                        @reverse Shape
                                                                                                        Pos (Peano Shape
                                                                                                                   Pos)
                                                                                                        x_1)) x_0)) xs)
                                                       (@id Shape Pos (List Shape Pos (Peano Shape Pos)) xs).

Definition prop_minus_plus_inv (Shape : Type) (Pos : Shape -> Type) (x
    : Free Shape Pos (Peano Shape Pos)) (y : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (Peano Shape Pos) (@comp Shape Pos (Peano Shape Pos) (Peano
                                        Shape Pos) (Peano Shape Pos) (pure (fun (a0
                                                                              : Free Shape Pos (Peano Shape Pos)) =>
                                                                              minus Shape Pos a0 y)) (pure (fun (a1
                                                                                                              : Free
                                                                                                                Shape
                                                                                                                Pos
                                                                                                                (Peano
                                                                                                                 Shape
                                                                                                                 Pos)) =>
                                                                                                              plus Shape
                                                                                                                   Pos y
                                                                                                                   a1))
                                                                     x) x.

Section section_append_0.
(* Constant arguments for append *)
Variable Shape : Type.
Variable Pos : Shape -> Type.
Variable a_0 : Type.
Variable a5_0 : Free Shape Pos (List Shape Pos a_0).
(* Helper functions for append *)
Fixpoint append_1 (a4 : List Shape Pos a_0) {struct a4} : Free Shape Pos (List
                                                                Shape Pos a_0)
           := match a4 with
              | nil => a5_0
              | cons a6 a7 =>
                  @Cons Shape Pos a_0 a6 (a7 >>=
                                       (fun (a7_0 : List Shape Pos a_0) => append_1 a7_0))
              end.
(* Main functions for append *)
Definition append_0 (a4 : Free Shape Pos (List Shape Pos a_0))
   : Free Shape Pos (List Shape Pos a_0) :=
  a4 >>= (fun (a4_0 : List Shape Pos a_0) => append_1 a4_0).
End section_append_0.

Definition append (Shape : Type) (Pos : Shape -> Type) {a : Type} (a4
    : Free Shape Pos (List Shape Pos a)) (a5 : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (List Shape Pos a) :=
  append_0 Shape Pos a a5 a4.

(* Helper functions for reverseNaive *)

Fixpoint reverseNaive_0 (Shape : Type) (Pos : Shape -> Type) {a : Type} (a10
                          : List Shape Pos a) {struct a10} : Free Shape Pos (List Shape Pos a)
           := match a10 with
              | nil => @Nil Shape Pos a
              | cons a11 a12 =>
                  @append Shape Pos a (a12 >>=
                                       (fun (a12_0 : List Shape Pos a) => @reverseNaive_0 Shape Pos a a12_0)) (@Cons
                                       Shape Pos a a11 (@Nil Shape Pos a))
              end.

Definition reverseNaive (Shape : Type) (Pos : Shape -> Type) {a : Type} (a10
    : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (List Shape Pos a) :=
  a10 >>= (fun (a10_0 : List Shape Pos a) => @reverseNaive_0 Shape Pos a a10_0).

Definition prop_reverse_is_reverseNaive (Shape : Type) (Pos : Shape -> Type) {a
   : Type} (xs : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (List Shape Pos a) (@reverse Shape Pos a xs) (@reverseNaive
                                        Shape Pos a xs).
