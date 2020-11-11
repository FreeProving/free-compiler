(** Operators that model call-by-value, call-by-name and call-by-need
   evaluation. *)

From Base Require Import Free.Class.Injectable.
From Base Require Import Free.Monad.
From Base Require Import Free.Instance.Share.
From Base Require Export Free.Strategy.CallByName.
From Base Require Export Free.Strategy.CallByNeed.
From Base Require Export Free.Strategy.CallByValue.

(* Instead of a type class for the evaluation strategy that provides an
   implementation for [share] and [call], we use a data type with one
   constructor for every supported evaluation strategy and implement
   [shape] and [call] by pattern matching. The advantage of this approach
   is that the data type is closed as opposed to type classes which are open.
   The closedness aids Coq's termination checker. *)
Inductive Strategy (Shape : Type) (Pos : Shape -> Type) : Type
  := Cbn : Strategy Shape Pos
   | Cbneed `{Injectable Share.Shape Share.Pos Shape Pos} : Strategy Shape Pos
   | Cbv : Strategy Shape Pos.

Arguments Cbn    {Shape} {Pos}.
Arguments Cbneed {Shape} {Pos} {_}.
Arguments Cbv    {Shape} {Pos}.

Definition shareWith (Shape : Type) (Pos : Shape -> Type)
                     (S : Strategy Shape Pos)
                     {A : Type}
                     (shareArgs : Strategy Shape Pos -> A -> Free Shape Pos A)
                     (fx : Free Shape Pos A)
 : Free Shape Pos (Free Shape Pos A)
  := match S with
     | Cbn    => shareByName Shape Pos fx
     | Cbneed => shareByNeed Shape Pos (shareArgs S) fx
     | Cbv    => shareByValue Shape Pos fx
     end.

Definition call (Shape : Type) (Pos : Shape -> Type)
                (S : Strategy Shape Pos)
                {A : Type}
                (fx : Free Shape Pos A)
 : Free Shape Pos (Free Shape Pos A)
  := match S with
     | Cbn    => callByName Shape Pos fx
     | Cbneed => callByNeed Shape Pos fx
     | Cbv    => callByValue Shape Pos fx
     end.
