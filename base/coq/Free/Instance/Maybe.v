(** * Definition of the maybe monad in terms of the free monad. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Util.Void.

Module Maybe.
  (* Container instance for a functor [One] with exactly one element. *)
  Definition Shape : Type := unit.
  Definition Pos (s : Shape) : Type := Void.

  (* Type synonym and smart constructors for the maybe monad. *)
  Module Import Monad.
    Definition Maybe (A : Type) : Type := Free Shape Pos A.

    (* The smart constructors embed the maybe effect in an effect stack *)
    Definition Just {A : Type}
                   (Shape' : Type)
                   (Pos' : Shape' -> Type)
                   `{Injectable Shape Pos Shape' Pos'}
                   (x : A)
      : Free Shape' Pos' A
     := pure x.

    Definition Nothing {A : Type}
                       (Shape' : Type)
                       (Pos' : Shape' -> Type)
                       `{Injectable Shape Pos Shape' Pos'}
       : Free Shape' Pos' A
      := impure (injS tt) (fun p : Pos' (injS tt) =>
      (fun (x : Void) => match x with end) (injP p)).
  End Monad.

  (* Handler for a program containing Maybe. *)
  Module Import Handler.
    Definition SMaybe (Shape' : Type) := Comb.Shape Shape Shape'.
    Definition PMaybe {Shape' : Type} (Pos' : Shape' -> Type)
    := Comb.Pos Pos Pos'.

    Fixpoint runMaybe {A : Type}
                      {Shape' : Type}
                      {Pos' : Shape' -> Type}
                      (fm : Free (SMaybe Shape') (PMaybe Pos') A)
     : Free Shape' Pos' (option A)
    := match fm with
       | pure x            => pure (Some x)
       | impure (inl s) _  => pure None
       | impure (inr s) pf => impure s (fun p : Pos' s => runMaybe (pf p))
       end.
  End Handler.

  (* Partial instance for the maybe monad. *)
  Instance Partial (Shape' : Type) (Pos' : Shape' -> Type)
                   `{Injectable Shape Pos Shape' Pos'}
    : Partial Shape' Pos' := {
      undefined := fun {A : Type}                => Nothing Shape' Pos';
      error     := fun {A : Type} (msg : string) => Nothing Shape' Pos'
    }.
End Maybe.


(* The type, smart constructors and handler should be visible to other modules
   but to use the shape, position function or partial instance the
   identifier must be fully qualified, i.e. [Maybe.Partial]. *)
Export Maybe.Handler.
Export Maybe.Monad.
