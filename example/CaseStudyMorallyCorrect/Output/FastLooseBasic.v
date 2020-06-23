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

Fixpoint rev_0 (Shape : Type) (Pos : Shape -> Type) {t0 : Type} (a0
                 : Free Shape Pos (List Shape Pos t0)) (a1 : List Shape Pos t0) {struct a1}
           : Free Shape Pos (List Shape Pos t0)
           := match a1 with
              | nil => a0
              | cons a2 a3 =>
                  a3 >>=
                  (fun (a3_0 : List Shape Pos t0) =>
                     @rev_0 Shape Pos t0 (@Cons Shape Pos t0 a2 a0) a3_0)
              end.

Definition rev (Shape : Type) (Pos : Shape -> Type) {t0 : Type} (a0
    : Free Shape Pos (List Shape Pos t0)) (a1 : Free Shape Pos (List Shape Pos t0))
   : Free Shape Pos (List Shape Pos t0) :=
  a1 >>= (fun (a1_0 : List Shape Pos t0) => @rev_0 Shape Pos t0 a0 a1_0).

Definition reverse (Shape : Type) (Pos : Shape -> Type) {a : Type} (xs
    : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (List Shape Pos a) :=
  @rev Shape Pos a (@Nil Shape Pos a) xs.

Definition prop_rev_is_rev_inv (Shape : Type) (Pos : Shape -> Type) {a : Type}
  (xs : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (List Shape Pos a) (@reverse Shape Pos a (@reverse Shape Pos a
                                                              xs)) xs.

Definition pred (Shape : Type) (Pos : Shape -> Type) (a12
    : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos (Peano Shape Pos) :=
  a12 >>=
  (fun a12_0 => match a12_0 with | zero => Zero Shape Pos | s a13 => a13 end).

Section section_map_0.
(* Constant arguments for map *)
Variable Shape : Type.
Variable Pos : Shape -> Type.
Variable a_0 b_0 : Type.
Variable a6_0 : Free Shape Pos (Free Shape Pos a_0 -> Free Shape Pos b_0).
(* Helper functions for map *)
Fixpoint map_1 (a7 : List Shape Pos a_0) {struct a7} : Free Shape Pos (List
                                                             Shape Pos b_0)
           := match a7 with
              | nil => @Nil Shape Pos b_0
              | cons a8 a9 =>
                  @Cons Shape Pos b_0 (a6_0 >>= (fun a6_1 => a6_1 a8)) (a9 >>=
                                       (fun (a9_0 : List Shape Pos a_0) => map_1 a9_0))
              end.
(* Main functions for map *)
Definition map_0 (a7 : Free Shape Pos (List Shape Pos a_0))
   : Free Shape Pos (List Shape Pos b_0) :=
  a7 >>= (fun (a7_0 : List Shape Pos a_0) => map_1 a7_0).
End section_map_0.

Definition map (Shape : Type) (Pos : Shape -> Type) {a b : Type} (a6
    : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b)) (a7
    : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (List Shape Pos b) :=
  map_0 Shape Pos a b a6 a7.

Definition id (Shape : Type) (Pos : Shape -> Type) {a : Type} (a0
    : Free Shape Pos a)
   : Free Shape Pos a :=
  a0.

Section section_foldPeano_0.
(* Constant arguments for foldPeano *)
Variable Shape : Type.
Variable Pos : Shape -> Type.
Variable a_0 : Type.
Variable a16_0 : Free Shape Pos a_0.
Variable a15_0 : Free Shape Pos (Free Shape Pos a_0 -> Free Shape Pos a_0).
(* Helper functions for foldPeano *)
Fixpoint foldPeano_1 (a17 : Peano Shape Pos) {struct a17} : Free Shape Pos a_0
           := match a17 with
              | zero => a16_0
              | s a18 =>
                  a15_0 >>=
                  (fun a15_1 =>
                     a15_1 (a18 >>= (fun (a18_0 : Peano Shape Pos) => foldPeano_1 a18_0)))
              end.
(* Main functions for foldPeano *)
Definition foldPeano_0 (a17 : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos a_0 :=
  a17 >>= (fun (a17_0 : Peano Shape Pos) => foldPeano_1 a17_0).
End section_foldPeano_0.

Definition foldPeano (Shape : Type) (Pos : Shape -> Type) {a : Type} (a15
    : Free Shape Pos (Free Shape Pos a -> Free Shape Pos a)) (a16
    : Free Shape Pos a) (a17 : Free Shape Pos (Peano Shape Pos))
   : Free Shape Pos a :=
  foldPeano_0 Shape Pos a a16 a15 a17.

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
