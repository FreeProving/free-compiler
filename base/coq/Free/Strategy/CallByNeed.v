From Base Require Import Free.Class.Injectable.
From Base Require Import Free.Monad.
From Base Require Import Free.Instance.Share.

Section SecCallByNeed.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Context `{Injectable Share.Shape Share.Pos Shape Pos}.

  Notation "'get'" := (Get Shape Pos).
  Notation "'put'" := (Put Shape Pos).
  Notation "'beginShare'" := (BeginShare Shape Pos).
  Notation "'endShare'" := (EndShare Shape Pos).

  Definition callByNeed {A : Type}
    (shareArgs : A -> Free Shape Pos A)
    (fx : Free Shape Pos A)
    : Free Shape Pos (Free Shape Pos A)
   := get >>= fun '(i,j) =>
      put (i+1,j) >>
      pure (beginShare (i,j) >>
            put (i,j+1) >>
            fx >>= fun x =>
            shareArgs x >>= fun x' =>
            put (i+1,j) >>
            endShare (i,j) >>
            pure x').
End SecCallByNeed.
