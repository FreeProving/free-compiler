(** * Definition of the error monad in terms of the free monad. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Util.Void.

Module Error.
  (* Container instance that corresponds to [Const]. *)
  Definition Shape (E : Type) : Type := E.
  Definition Pos {E : Type} (s : Shape E) : Type := Void.

  (* Type synonym and smart constructors for the error monad. *)
  Module Import Monad.
    Definition Error (E A : Type) := Free (Shape E) Pos A.

    (* The smart constructors embed the error effect in an effect stack *)
    Definition NoError (Shape' : Type) (Pos' : Shape' -> Type)
                       {E A : Type}
                       `{Injectable (Shape E) Pos Shape' Pos'}
                       (x : A) : Free Shape' Pos' A := pure x.

    Definition ThrowError (Shape' : Type) (Pos' : Shape' -> Type)
                          {E A : Type}
                          `{Injectable (Shape E) Pos Shape' Pos'}
                          (msg : E) : Free Shape' Pos' A :=
      impure (injS msg) (fun p : Pos' (injS msg) =>
                          (fun x : Void => match x with end) (injP p)).
  End Monad.

  (* Handler for the error monad. *)
  Module Import Handler.
  Section SecErrorHandler.
    Context {Shape' : Type}.
    Context {Pos'   : Shape' -> Type}.

    Notation "'FreeComb'" := (Free (Comb.Shape (Shape string) Shape') (Comb.Pos Pos Pos')).
    Notation "'Free''" := (Free Shape' Pos').

    (* The result is either a value of type A or an error message of type E. *)
    Fixpoint runError {A : Type} (fx : FreeComb A) : Free' (A + string)
     := match fx with
        | pure x => pure (inl x)
        | impure (inl s) _  => pure (inr s)
        | impure (inr s) pf => impure s (fun p => runError (pf p))
        end.

    (* When proving properties about partial computations, consider failed
       constructions of properties as false. *)
    Definition runErrorProp (fx : FreeComb Prop) : Free' Prop
     := runError fx >>= fun ex => match ex with
                                  | inl x => pure x
                                  | inr _ => pure False
                                  end.
  End SecErrorHandler.
  End Handler.

  (* Partial instance for the error monad. *)
  Instance Partial (Shape' : Type) (Pos' : Shape' -> Type)
                   `{Injectable (Shape string) Pos Shape' Pos'}
                   : Partial Shape' Pos' := {
    undefined := fun {A : Type}                => ThrowError Shape' Pos' "undefined"%string;
    error     := fun {A : Type} (msg : string) => ThrowError Shape' Pos' msg
  }.
End Error.


(* The type and smart constructor should be visible to other modules
   but to use the shape or position function the identifier must be
   fully qualified, i.e. [Error.Partial]. *)
Export Error.Handler.
Export Error.Monad.
