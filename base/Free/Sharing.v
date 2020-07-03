From Base Require Import Free.Monad.

(** An effect-generic (non-functional) sharing operator.
    The final operator will not be able to operate on arbitrary 
    shapes and position functions but will require the state and 
    sharing effects to be present.
    The operator will eventually also require A to be an instance 
    of a type class Shareable. *)
Definition share {A : Type} {Shape : Type} {Pos : Shape -> Type}
  (p : Free Shape Pos A) 
  : Free Shape Pos (Free Shape Pos A) := 
  pure p.

(** An effect-generic (non-functional) sharing operator that models 
    call-by-value instead of call-by-name, that is, it evaluates its
    program argument immediately. *)
Definition share' {A : Type} {Shape : Type} {Pos : Shape -> Type} (p : Prog Shape Pos A) 
  : Free Shape Pos (Free Shape Pos A) :=
  p >>= fun x => pure (pure x).