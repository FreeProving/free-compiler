(* module Proofs.AppendAssoc *)

From Base Require Import Free.

From Base Require Import Prelude.

From Base Require Import Test.QuickCheck.

Section section_append_0.
(* Constant arguments for append *)
Variable Shape : Type.
Variable Pos : Shape -> Type.
Variable a_0 : Type.
Variable ys_0 : Free Shape Pos (List Shape Pos a_0).
(* Helper functions for append *)
Fixpoint append_1 (xs : List Shape Pos a_0) {struct xs} : Free Shape Pos (List
                                                                Shape Pos a_0)
           := match xs with
              | nil => ys_0
              | cons x xs' =>
                  @Cons Shape Pos a_0 x (xs' >>=
                                       (fun (xs'_0 : List Shape Pos a_0) => append_1 xs'_0))
              end.
(* Main functions for append *)
Definition append_0 (xs : Free Shape Pos (List Shape Pos a_0))
   : Free Shape Pos (List Shape Pos a_0) :=
  xs >>= (fun (xs_0 : List Shape Pos a_0) => append_1 xs_0).
End section_append_0.

Definition append (Shape : Type) (Pos : Shape -> Type) {a : Type} (xs
    : Free Shape Pos (List Shape Pos a)) (ys : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (List Shape Pos a) :=
  append_0 Shape Pos a ys xs.

Definition prop_append_assoc (Shape : Type) (Pos : Shape -> Type) {a : Type} (xs
    : Free Shape Pos (List Shape Pos a)) (ys : Free Shape Pos (List Shape Pos a))
  (zs : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (List Shape Pos a) (@append Shape Pos a xs (@append Shape Pos
                                                             a ys zs)) (@append Shape Pos a (@append Shape Pos a xs ys)
                                                                                            zs).

Definition prop_append_nil (Shape : Type) (Pos : Shape -> Type) {a : Type} (xs
    : Free Shape Pos (List Shape Pos a))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (List Shape Pos a) (@append Shape Pos a xs (@Nil Shape Pos a))
                                       xs.
