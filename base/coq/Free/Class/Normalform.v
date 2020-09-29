(** Type class for the normalization of data types with effectful components.
    Moves effects from components to the root of the expression.
    This implementation is based on the following implementation:
    https://github.com/nbun/mathesis/blob/master/Coq/src/Classes.v *)

From Base Require Import Free.Monad.

From Base Require Import Free.Instance.Identity.

Class Normalform (Shape : Type) (Pos : Shape -> Type)
                 (A : Type) :=
  {
    (** The normalized return type. *)
    nType : Type;
    (** The function is split into two parts due to termination check errors
        for recursive data types. *)
    nf' : A -> Free Shape Pos nType
  }.

(* Normalizes a Free value. *)
Definition nf {Shape : Type} {Pos : Shape -> Type} {A : Type}
                  `{Normalform Shape Pos A} (n : Free Shape Pos A)
 : Free Shape Pos nType
:= n >>= nf'.

Lemma nfImpure {Shape : Type} {Pos : Shape -> Type} {A : Type}
                     `{Normalform Shape Pos A}
  : forall s (pf : _ -> Free Shape Pos A),
  nf (impure s pf) = impure s (fun p => nf (pf p)).
Proof. trivial. Qed.

Lemma nfPure {Shape : Type} {Pos : Shape -> Type} {A : Type}
                     `{Normalform Shape Pos A} : forall (x : A),
  nf (pure x) = nf' x.
Proof. trivial. Qed.

(* Normalform instance for functions.
   Effects inside of functions are not pulled to the root. *)
Instance NormalformFunc (Shape : Type) (Pos : Shape -> Type) (A B : Type)
 : Normalform Shape Pos (A -> B) :=
  { nf' := pure }.
