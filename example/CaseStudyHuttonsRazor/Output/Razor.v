(* module Razor *)

From Base Require Import Free.

From Base Require Import Prelude.

From Base Require Import Test.QuickCheck.

From Generated Require Export Proofs.AppendAssoc.

Definition Stack (Shape : Type) (Pos : Shape -> Type) : Type :=
  List Shape Pos (Integer Shape Pos).

(* Data type declarations for Op *)

Inductive Op (Shape : Type) (Pos : Shape -> Type) : Type
  := push : Free Shape Pos (Integer Shape Pos) -> Op Shape Pos
  |  add : Op Shape Pos.

(* Arguments sentences for Op *)

Arguments push {Shape} {Pos}.

Arguments add {Shape} {Pos}.

(* Smart constructors for Op *)

Definition PUSH (Shape : Type) (Pos : Shape -> Type) (x_0
    : Free Shape Pos (Integer Shape Pos))
   : Free Shape Pos (Op Shape Pos) :=
  pure (push x_0).

Definition ADD (Shape : Type) (Pos : Shape -> Type)
   : Free Shape Pos (Op Shape Pos) :=
  pure add.

(* Data type declarations for Expr *)

Inductive Expr (Shape : Type) (Pos : Shape -> Type) : Type
  := val : Free Shape Pos (Integer Shape Pos) -> Expr Shape Pos
  |  add0
   : Free Shape Pos (Expr Shape Pos) ->
     Free Shape Pos (Expr Shape Pos) -> Expr Shape Pos.

(* Arguments sentences for Expr *)

Arguments val {Shape} {Pos}.

Arguments add0 {Shape} {Pos}.

(* Smart constructors for Expr *)

Definition Val (Shape : Type) (Pos : Shape -> Type) (x_0
    : Free Shape Pos (Integer Shape Pos))
   : Free Shape Pos (Expr Shape Pos) :=
  pure (val x_0).

Definition Add0 (Shape : Type) (Pos : Shape -> Type) (x_0
    : Free Shape Pos (Expr Shape Pos)) (x_1 : Free Shape Pos (Expr Shape Pos))
   : Free Shape Pos (Expr Shape Pos) :=
  pure (add0 x_0 x_1).

Definition Code (Shape : Type) (Pos : Shape -> Type) : Type :=
  List Shape Pos (Op Shape Pos).

(* Helper functions for exec *)

Fixpoint exec_0 (Shape : Type) (Pos : Shape -> Type) (P : Partial Shape Pos) (a7
                  : Code Shape Pos) (a8 : Free Shape Pos (Stack Shape Pos)) {struct a7} : Free
                                                                                          Shape Pos (Stack Shape Pos)
           := match a7 with
              | nil =>
                  a8 >>=
                  (fun a8_3 =>
                     match a8_3 with
                     | nil => @Nil Shape Pos (Integer Shape Pos)
                     | cons a9 a10 => @Cons Shape Pos (Integer Shape Pos) a9 a10
                     end)
              | cons a13 a14 =>
                  a13 >>=
                  (fun a13_0 =>
                     match a13_0 with
                     | push a21 =>
                         a8 >>=
                         (fun a8_3 =>
                            match a8_3 with
                            | nil =>
                                a14 >>=
                                (fun (a14_0 : Code Shape Pos) =>
                                   exec_0 Shape Pos P a14_0 (@Cons Shape Pos (Integer Shape Pos) a21 (@Nil Shape
                                                                                                  Pos (Integer Shape
                                                                                                               Pos))))
                            | cons a24 a25 =>
                                a14 >>=
                                (fun (a14_0 : Code Shape Pos) =>
                                   exec_0 Shape Pos P a14_0 (@Cons Shape Pos (Integer Shape Pos) a21 (@Cons Shape
                                                                                                  Pos (Integer Shape
                                                                                                               Pos) a24
                                                                                                                    a25)))
                            end)
                     | add =>
                         a8 >>=
                         (fun a8_3 =>
                            match a8_3 with
                            | cons a28 a29 =>
                                a29 >>=
                                (fun a29_0 =>
                                   match a29_0 with
                                   | cons a32 a33 =>
                                       a14 >>=
                                       (fun (a14_0 : Code Shape Pos) =>
                                          exec_0 Shape Pos P a14_0 (@Cons Shape Pos (Integer Shape Pos) (addInteger
                                                                                                         Shape Pos a32
                                                                                                         a28) a33))
                                   | nil => @undefined Shape Pos P (Stack Shape Pos)
                                   end)
                            | nil => @undefined Shape Pos P (Stack Shape Pos)
                            end)
                     end)
              end.

Definition exec (Shape : Type) (Pos : Shape -> Type) (P : Partial Shape Pos) (a7
    : Free Shape Pos (Code Shape Pos)) (a8 : Free Shape Pos (Stack Shape Pos))
   : Free Shape Pos (Stack Shape Pos) :=
  a7 >>= (fun (a7_0 : Code Shape Pos) => exec_0 Shape Pos P a7_0 a8).

(* Helper functions for eval *)

Fixpoint eval_0 (Shape : Type) (Pos : Shape -> Type) (a0 : Expr Shape Pos)
                {struct a0} : Free Shape Pos (Integer Shape Pos)
           := match a0 with
              | val a1 => a1
              | add0 a3 a4 =>
                  addInteger Shape Pos (a3 >>=
                              (fun (a3_0 : Expr Shape Pos) => eval_0 Shape Pos a3_0)) (a4 >>=
                              (fun (a4_0 : Expr Shape Pos) => eval_0 Shape Pos a4_0))
              end.

Definition eval (Shape : Type) (Pos : Shape -> Type) (a0
    : Free Shape Pos (Expr Shape Pos))
   : Free Shape Pos (Integer Shape Pos) :=
  a0 >>= (fun (a0_0 : Expr Shape Pos) => eval_0 Shape Pos a0_0).

(* Helper functions for compApp *)

Fixpoint compApp_0 (Shape : Type) (Pos : Shape -> Type) (a43 : Expr Shape Pos)
                   (a44 : Free Shape Pos (Code Shape Pos)) {struct a43} : Free Shape Pos (Code
                                                                                Shape Pos)
           := match a43 with
              | val a45 => @Cons Shape Pos (Op Shape Pos) (PUSH Shape Pos a45) a44
              | add0 a47 a48 =>
                  a47 >>=
                  (fun (a47_0 : Expr Shape Pos) =>
                     compApp_0 Shape Pos a47_0 (a48 >>=
                                (fun (a48_0 : Expr Shape Pos) =>
                                   compApp_0 Shape Pos a48_0 (@Cons Shape Pos (Op Shape Pos) (ADD Shape Pos)
                                                                                             a44))))
              end.

Definition compApp (Shape : Type) (Pos : Shape -> Type) (a43
    : Free Shape Pos (Expr Shape Pos)) (a44 : Free Shape Pos (Code Shape Pos))
   : Free Shape Pos (Code Shape Pos) :=
  a43 >>= (fun (a43_0 : Expr Shape Pos) => compApp_0 Shape Pos a43_0 a44).

Definition comp' (Shape : Type) (Pos : Shape -> Type) (e
    : Free Shape Pos (Expr Shape Pos))
   : Free Shape Pos (Code Shape Pos) :=
  compApp Shape Pos e (@Nil Shape Pos (Op Shape Pos)).

Definition prop_comp'_correct (Shape : Type) (Pos : Shape -> Type) (P
    : Partial Shape Pos) (e : Free Shape Pos (Expr Shape Pos))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (Stack Shape Pos) (exec Shape Pos P (comp' Shape Pos e) (@Nil
                                             Shape Pos (Integer Shape Pos))) (@Cons Shape Pos (Integer Shape Pos) (eval
                                                                                                                   Shape
                                                                                                                   Pos
                                                                                                                   e)
                                                                                                                  (@Nil
                                                                                                                   Shape
                                                                                                                   Pos
                                                                                                                   (Integer
                                                                                                                    Shape
                                                                                                                    Pos))).

(* Helper functions for comp *)

Fixpoint comp_0 (Shape : Type) (Pos : Shape -> Type) (a36 : Expr Shape Pos)
                {struct a36} : Free Shape Pos (Code Shape Pos)
           := match a36 with
              | val a37 =>
                  @Cons Shape Pos (Op Shape Pos) (PUSH Shape Pos a37) (@Nil Shape Pos (Op Shape
                                                                                          Pos))
              | add0 a39 a40 =>
                  @append Shape Pos (Op Shape Pos) (@append Shape Pos (Op Shape Pos) (a39 >>=
                                                                                      (fun (a39_0 : Expr Shape Pos) =>
                                                                                         comp_0 Shape Pos a39_0)) (a40
                                                                                      >>=
                                                                                      (fun (a40_0 : Expr Shape Pos) =>
                                                                                         comp_0 Shape Pos a40_0)))
                                                   (@Cons Shape Pos (Op Shape Pos) (ADD Shape Pos) (@Nil Shape Pos (Op
                                                                                     Shape Pos)))
              end.

Definition comp (Shape : Type) (Pos : Shape -> Type) (a36
    : Free Shape Pos (Expr Shape Pos))
   : Free Shape Pos (Code Shape Pos) :=
  a36 >>= (fun (a36_0 : Expr Shape Pos) => comp_0 Shape Pos a36_0).

Definition prop_comp_comp'_eq (Shape : Type) (Pos : Shape -> Type) (e
    : Free Shape Pos (Expr Shape Pos))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (Code Shape Pos) (comp Shape Pos e) (comp' Shape Pos e).

Definition prop_comp_correct (Shape : Type) (Pos : Shape -> Type) (P
    : Partial Shape Pos) (e : Free Shape Pos (Expr Shape Pos))
   : Free Shape Pos (Property Shape Pos) :=
  @eqProp Shape Pos (Stack Shape Pos) (exec Shape Pos P (comp Shape Pos e) (@Nil
                                             Shape Pos (Integer Shape Pos))) (@Cons Shape Pos (Integer Shape Pos) (eval
                                                                                                                   Shape
                                                                                                                   Pos
                                                                                                                   e)
                                                                                                                  (@Nil
                                                                                                                   Shape
                                                                                                                   Pos
                                                                                                                   (Integer
                                                                                                                    Shape
                                                                                                                    Pos))).
