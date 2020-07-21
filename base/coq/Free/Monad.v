Section SecFree.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Inductive Free (A : Type) : Type :=
    | pure : A -> Free A
    | impure : forall (s : Shape), (Pos s -> Free A) -> Free A.

  Arguments pure {A}.
  Arguments impure {A}.

  Section free_bind'.
    Variable A B : Type.
    Variable f: A -> Free B.

    Fixpoint free_bind' (mx: Free A) : Free B :=
      match mx with
      | pure x => f x
      | impure s pf => impure s (fun x => free_bind' (pf x))
      end.

  End free_bind'.

  Definition free_bind {A B : Type} (mx: Free A) (f: A -> Free B) : Free B :=
    free_bind' A B f mx.

End SecFree.

(* The arguments of the constructors of the free monad are implicit. *)
Arguments pure {Shape} {Pos} {A}.
Arguments impure {Shape} {Pos} {A}.

(* The arguments of the bind operation are implicit and we
   introduce the infix notation for the bind operator. *)
Arguments free_bind {Shape} {Pos} {A} {B}.
Notation "mx >>= f" := (free_bind mx f) (left associativity, at level 50).
Notation "mx >> my" := (free_bind mx (fun _ => my)) (left associativity, at level 50).
