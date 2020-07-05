(** * Definition of the identity monad in terms of the free monad. *)

From Base Require Import Free.
From Base Require Import Free.Util.Void.

Module Identity.
  (* Container instance for a functor [Zero] with no elements. *)
  Definition Shape : Type := Void.
  Definition Pos (s : Shape) : Type := Void.

  (* Type synonym and smart constructors for the identity monad. *)
  Module Import Monad.
    Definition Identity (A : Type) : Type := Free Shape Pos A.
    Definition Id {Shape' : Type} {Pos' : Shape' -> Type} {A : Type} 
    `{Injectable Shape Pos Shape' Pos'} (x : A) 
    : Free Shape' Pos' A := pure x.
  End Monad.

  (* There is no partial instance for the identity monad. *)
End Identity.

(* The type and smart constructor should be visible to other modules
   but to use the shape or position function the identifier must be
   fully qualified, i.e. [Identity.Shape]. *)
Export Identity.Monad.
