From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Instance.Share.
From Base Require Import Free.Instance.State.
From Base Require Import Free.Monad.

(* For testing *)
From Base Require Import Free.Instance.Identity.
From Base Require Import Prelude.

(* A shape with the Share and State effect shapes wrapped around it. *)
Definition SShape (Shape : Type) : Type := Comb.Shape State.Shape (Comb.Shape Share.Shape Shape).

(* A position function with the Share and State effect position functions wrapped around it. *)
Definition SPos {Shape : Type} (Pos : Shape -> Type) : SShape Shape -> Type := 
  Comb.Pos State.Pos (Comb.Pos Share.Pos Pos).

(* The type of a shared variable or expression of type Free Shape Pos A*)
Definition SComb (Shape : Type) (Pos : Shape -> Type) (A : Type) := Free (SShape Shape) (SPos Pos) A.

(* An effect-generic (non-functional) sharing operator for an already lifted variable or expression. *)
(* Will eventually also require A to be an instance of Shareable. *)
Definition share {A : Type} {Shape : Type} {Pos : Shape -> Type}
  (x : Free (SShape Shape) (SPos Pos) A) 
  : Free (SShape Shape) (SPos Pos) (SComb Shape Pos A) := 
  pure x.

(* A function to lift a Free value into the sharing setting. *)
Definition liftS {A : Type} {Shape : Type} {Pos : Shape -> Type} (x : Free Shape Pos A) 
  : SComb Shape Pos A :=
  Comb.Monad.Inr (Comb.Monad.Inr x).

(* An effect-generic (non-functional) sharing operator for a non-lifted variable or expression. *)
(* Will eventually also require A to be an instance of Shareable. *)
(* I'm not sure if it's going to be useful at all. *)
Definition share' {A : Type} {Shape : Type} {Pos : Shape -> Type} (x : Free Shape Pos A) 
  : Free (SShape Shape) (SPos Pos) (SComb Shape Pos A) :=
  pure (liftS x).


(* Testing *)

Definition n : Integer Identity.Shape Identity.Pos := 1%Z.

(* Doubling an integer without sharing. *)
Definition double {Shape : Type} {Pos : Shape -> Type} (x : Free Shape Pos (Integer Shape Pos)) := 
   addInteger Shape Pos x x.

Compute double (pure n).

(* Doubling an integer that is shared. *)
(* Note that we need to wrap the shape and position function with SShape and SPos. *)
Definition doubleShare {Shape : Type} {Pos : Shape -> Type} (x : SComb Shape Pos (Integer Shape Pos)) := 
   share x >>= fun sx => addInteger (SShape Shape) (SPos Pos) sx sx.

Compute doubleShare (liftS (pure n)).
