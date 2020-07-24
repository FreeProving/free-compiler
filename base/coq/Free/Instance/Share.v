(** * Definition of the sharing effect in terms of the free monad. *)

From Base Require Import Free.

Module Share.

  (* Shape and position function *)
  Inductive Shape : Type := 
  | sget : Shape
  | sput : (nat * nat) -> Shape
  | sbsharing : (nat * nat) -> Shape 
  | sesharing : (nat * nat) -> Shape.

  Definition Pos (s : Shape) : Type := 
    match s with 
    | sget   => (nat * nat)
    | _ => unit
    end.

  (* Type synonym and smart constructors for the sharing effect. *)
  Module Import Monad.
    Definition Share (A : Type) : Type := Free Shape Pos A.

    Definition Get (Shape' : Type) (Pos' : Shape' -> Type) 
    `{Injectable Shape Pos Shape' Pos'} 
    : Free Shape' Pos' (nat * nat) :=
    impure (injS sget) (fun p => pure (injP p)).

    Definition Put (Shape' : Type) (Pos' : Shape' -> Type) (n : nat * nat) 
    `{Injectable Shape Pos Shape' Pos'} 
    : Free Shape' Pos' unit :=
    impure (injS (sput n)) (fun _ => pure tt).

    Definition BeginShare (Shape' : Type) (Pos' : Shape' -> Type) (n : nat * nat)
    `{Injectable Shape Pos Shape' Pos'} 
    : Free Shape' Pos' unit :=
    impure (injS (sbsharing n)) (fun _ => pure tt).

    Definition EndShare (Shape' : Type) (Pos' : Shape' -> Type) (n : nat * nat)
    `{Injectable Shape Pos Shape' Pos'} 
    : Free Shape' Pos' unit :=
    impure (injS (sesharing n)) (fun _ => pure tt).
  End Monad.
End Share.

Export Share.Monad.
