(** * Definition of the error monad in terms of the free monad. *)

From Base Require Import Free.
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

  (* Partial instance for the error monad. *)
  Instance Partial : Partial (Shape string) Pos := {
    undefined := fun {A : Type}                => ThrowError "undefined"%string;
    error     := fun {A : Type} (msg : string) => ThrowError msg
  }.
End Error.

(* The type and smart constructor should be visible to other modules
   but to use the shape or position function the identifier must be
   fully qualified, i.e. [Error.Partial]. *)
Export Error.Monad.
