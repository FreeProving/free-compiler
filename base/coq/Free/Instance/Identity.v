(** * Definition of the identity monad in terms of the free monad. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Util.Void.

Module Identity.
  (* Container instance for a functor [Zero] with no elements. *)
  Definition Shape : Type := Void.
  Definition Pos (s : Shape) : Type := Void.

  (* Type synonym and smart constructors for the identity monad. *)
  Module Import Monad.
    Definition Identity (A : Type) : Type := Free Shape Pos A.
    (* Smart constructor that embeds the Identity effect in an effect stack. *)
    Definition Id {A : Type}
                  (Shape' : Type)
                  (Pos' : Shape' -> Type)
                  `{Injectable Shape Pos Shape' Pos'}
                  (x : A)
    : Free Shape' Pos' A := pure x.
  End Monad.
 
  (* Handler for an effect-free program. *)
  Module Import Handler.
    Definition run {A : Type} (fz : Free Identity.Shape Identity.Pos A) : A
      := match fz with
         | pure x => x
         | impure s _ => match s with end
         end.
  End Handler.
  (* There is no partial instance for the identity monad. *)
End Identity.

(* The type, smart constructor and handler should be visible to other modules
   but to use the shape or position function the identifier must be
   fully qualified, i.e. [Identity.Shape]. *)
Export Identity.Handler.
Export Identity.Monad.
