(** Type class for the normalization of data types with effectful components.
    Moves effects from components to the root of the expression. 
    This implementation is based on the following implementation:
    https://github.com/nbun/mathesis/blob/master/Coq/src/Classes.v *)

From Base Require Import Free.Monad.

Class Normalform (Shape : Type) (Pos : Shape -> Type)
                 (A B : Type) :=
  {
    (** The function is split into two parts due to termination check errors
        for recursive data types. *)
    nf' : A -> Free Shape Pos B
  }.

Definition nf {Shape : Type} {Pos : Shape -> Type} {A B : Type}
                  `{Normalform Shape Pos A B} (n : Free Shape Pos A)
 : Free Shape Pos B
:= n >>= nf'.

Lemma nfImpure {Shape : Type} {Pos : Shape -> Type} {A B : Type}
                     `{Normalform Shape Pos A B}
  : forall s (pf : _ -> Free Shape Pos A), 
  nf (impure s pf) = impure s (fun p => nf (pf p)).
Proof. trivial. Qed.

Lemma nfPure {Shape : Type} {Pos : Shape -> Type} {A B : Type}
                     `{Normalform Shape Pos A B} : forall (x : A),
  nf (pure x) = nf' x.
Proof. trivial. Qed.

(* Normalform instance for functions.
   Effects inside of functions are not pulled to the root. *)
Instance NormalformFunc (Shape : Type) (Pos : Shape -> Type) (A B : Type) 
 : Normalform Shape Pos (A -> B) (A -> B) :=
  { nf' := pure }.