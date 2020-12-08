(** Operators that model call-by-value, call-by-name and call-by-need
   evaluation. *)

From Base Require Import Free.Class.Injectable.
From Base Require Import Free.Monad.
From Base Require Import Free.Instance.Share.
From Base Require Export Free.Strategy.CallByName.
From Base Require Export Free.Strategy.CallByNeed.
From Base Require Export Free.Strategy.CallByValue.

(* Instead of a type class for the evaluation strategy that provides an
   implementation for [share], we use a data type with one constructor for
   every supported evaluation strategy and implement [shape] by pattern
   matching. The advantage of this approach is that the data type is closed as
   opposed to type classes which are open.
   The closedness aids Coq's termination checker. *)
Inductive Strategy (Shape : Type) (Pos : Shape -> Type) : Type
  := cbn : Strategy Shape Pos
   | cbneed `{Injectable Share.Shape Share.Pos Shape Pos} : Strategy Shape Pos
   | cbv : Strategy Shape Pos.

Arguments cbn    {Shape} {Pos}.
Arguments cbneed {Shape} {Pos} {_}.
Arguments cbv    {Shape} {Pos}.

(* Smart constructors with explicit arguments for [Shape] and [Pos].
   These are intended to be used in conjunction with
   [Test.QuickCheck.withStrategy] such that the implicit arguments don't
   have to be made explicit with [@] (which would require extra parenteses). *)
Definition Cbn    (Shape : Type) (Pos : Shape -> Type) : Strategy Shape Pos := cbn.
Definition Cbneed (Shape : Type) (Pos : Shape -> Type)
                  `{Injectable Share.Shape Share.Pos Shape Pos}
                  : Strategy Shape Pos := cbneed.
Definition Cbv    (Shape : Type) (Pos : Shape -> Type) : Strategy Shape Pos := cbv.

(* Allow Coq to expand the definition of the smart constructor when simplifying
   terms. *)
Arguments Cbn    Shape Pos /.
Arguments Cbneed Shape Pos {_} /.
Arguments Cbv    Shape Pos /.

Definition shareWith (Shape : Type) (Pos : Shape -> Type)
                     (S : Strategy Shape Pos)
                     {A : Type}
                     (shareArgs : Strategy Shape Pos -> A -> Free Shape Pos A)
                     (fx : Free Shape Pos A)
 : Free Shape Pos (Free Shape Pos A)
  := match S with
     | cbn    => callByName Shape Pos fx
     | cbneed => callByNeed Shape Pos (shareArgs S) fx
     | cbv    => callByValue Shape Pos fx
     end.
