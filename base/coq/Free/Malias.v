(** Operators that model call-by-value, call-by-name and call-by-need
   evaluation. *)

From Base Require Import Free.Class.Injectable.
From Base Require Import Free.Class.ShareableArgs.
From Base Require Import Free.Class.Strategy.
From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Instance.Share.
From Base Require Import Free.Monad.

(* An operator to model call-by-value evaluation *)
Definition cbv {A : Type} (Shape : Type) (Pos : Shape -> Type) (p : Free Shape Pos A)
  : Free Shape Pos (Free Shape Pos A) :=
  p >>= fun x => pure (pure x).

(* An operator to model call-by-name evaluation *)
Definition cbn {A : Type} (Shape : Type) (Pos : Shape -> Type)
  (p : Free Shape Pos A)
  : Free Shape Pos (Free Shape Pos A) :=
  pure p.

Section SecCbneed.

Variable Shape : Type.
Variable Pos : Shape -> Type.
Context `{Injectable Share.Shape Share.Pos Shape Pos}.

Notation "'Get''" := (Get Shape Pos).
Notation "'Put''" := (Put Shape Pos).
Notation "'BeginShare''" := (BeginShare Shape Pos).
Notation "'EndShare''" := (EndShare Shape Pos).

Definition cbneed {A : Type} (fx : Free Shape Pos A)
  : Free Shape Pos (Free Shape Pos A)
 := Get' >>= fun '(i,j) =>
    Put' (i+1,j) >>
    pure (BeginShare' (i,j) >>
          Put' (i,j+1) >>
          fx >>= fun x =>
          Put' (i+1,j) >>
          EndShare' (i,j) >>
          pure x).

End SecCbneed.

(* Strategy instances for different evaluation strategies *)

(* Strategy instance for call-by-need evaluation. *)
Instance Cbneed {Shape : Type} {Pos : Shape -> Type}
                `{I : Injectable Share.Shape Share.Pos Shape Pos}
  : Strategy Shape Pos | 1
 := { shareWith' A _ := @cbneed Shape Pos I A }.

(* Strategy instance for call-by-name evaluation. *)
Instance Cbn {Shape : Type} {Pos : Shape -> Type}
  : Strategy Shape Pos | 2
 := { shareWith' A fx _ := @cbn A Shape Pos fx }.

(* Strategy instance for call-by-value evaluation. *)
Instance Cbv {Shape : Type} {Pos : Shape -> Type}
  : Strategy Shape Pos | 2
 := { shareWith' A fx _ := @cbv A Shape Pos fx }.
