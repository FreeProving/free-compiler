(** Type class for the normalization of data types with effectful components.
    Moves effects from components to the root of the expression. 
    This implementation is based on the following implementation:
    https://github.com/nbun/mathesis/blob/master/Coq/src/Classes.v *)

From Base Require Import Free.Monad.

Class Normalform {Shape : Type} {Pos : Shape -> Type}
                 (A B : Type) :=
  {
    (** The function is split into two parts due to termination check errors
        for recursive data types. *)
    nf  : Free Shape Pos A -> Free Shape Pos B;
    nf' : A -> Free Shape Pos B;
    (** Property for moving nf into position functions *)
    nf_impure: forall s (pf : _ -> Free Shape Pos A),
        nf (impure s pf) = impure s (fun p => nf (pf p));
    (** Property for unfolding nf on pure values *)
    nf_pure : forall (x : A),
        nf (pure x) = nf' x
  }.