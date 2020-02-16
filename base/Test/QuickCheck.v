From Base Require Import Free.
From Base Require Import Prelude.

(* QuickCheck properties are implemented as Coq propositions. *)
Definition Property (Shape : Type) (Pos : Shape -> Type) := Prop.

(* Utility function to convert a boolean value to a proposition. *)
Definition isPureTrue (Shape : Type) (Pos : Shape -> Type)
                      (b : Free Shape Pos (Bool Shape Pos))
  : Prop
 := b = True_ Shape Pos.

(* Since the left hand side of QuickCheck's [==>] operator must be a
   boolean, we need this helper function to convert it to a proposition. *)
Definition precondition (Shape : Type) (Pos : Shape -> Type)
                        (b : Free Shape Pos (Bool Shape Pos))
                        (p : Prop)
  : Prop
 := isPureTrue Shape Pos b -> p.

(* Coq cannot infer the type of the operands of [=] and [<>] in some cases.
  Thus, we have to add this helper function which constrains the
  type as well as the [Shape] and [Pos] arguments. *)
Definition eqProp (Shape : Type) (Pos : Shape -> Type) {a : Type}
                  (x : Free Shape Pos a) (y : Free Shape Pos a)
  : Prop
 := x = y.

Definition neqProp (Shape : Type) (Pos : Shape -> Type) {a : Type}
                   (x : Free Shape Pos a) (y : Free Shape Pos a)
  : Prop
 := x <> y.
