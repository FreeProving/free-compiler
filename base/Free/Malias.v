(** Operators that model call-by-value, call-by-name and call-by-need 
   evaluation. *)

From Base Require Import Free.
From Base Require Export Free.Instance.Comb.
From Base Require Export Free.Instance.Share.

(** An operator to model call-by-value evaluation *)
Definition cbv {A : Type} {Shape : Type} {Pos : Shape -> Type} (p : Free Shape Pos A) 
  : Free Shape Pos (Free Shape Pos A) :=
  p >>= fun x => pure (pure x).

(** An operator to model call-by-name evaluation *)
Definition cbn {A : Type} {Shape : Type} {Pos : Shape -> Type}
  (p : Free Shape Pos A) 
  : Free Shape Pos (Free Shape Pos A) := 
  pure p.

Definition cbneed {A : Type} {Shape : Type} {Pos : Shape -> Type}
  `{Injectable Share.Shape Share.Pos Shape Pos} (p : Free Shape Pos A)
  : Free Shape Pos (Free Shape Pos A) :=
  Get >>= fun '(i,j) =>
  Put (i + 1, j) >>
  pure (BeginShare (i,j) >>
      Put (i, j+1) >>
      p >>= fun x =>
      Put (i+1,j) >>
      EndShare (i,j) >>
      pure x).