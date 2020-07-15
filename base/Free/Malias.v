(** Operators that model call-by-value, call-by-name and (eventually) call-by-need 
   evaluation. *)

From Base Require Import Free.Monad.

(** An operator to model call-by-value evaluation *)
Definition cbv {A : Type} {Shape : Type} {Pos : Shape -> Type} (p : Free Shape Pos A) 
  : Free Shape Pos (Free Shape Pos A) :=
  p >>= fun x => pure (pure x).

(** An operator to model call-by-name evaluation *)
Definition cbn {A : Type} {Shape : Type} {Pos : Shape -> Type}
  (p : Free Shape Pos A) 
  : Free Shape Pos (Free Shape Pos A) := 
  pure p.