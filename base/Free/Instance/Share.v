(** * Definition of the sharing effect in terms of the free monad. *)

From Base Require Import Free.
From Base Require Export Free.Util.Sharing.

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

    Definition Get {Shape' : Type} {Pos' : Shape' -> Type} 
    `{Injectable Shape Pos Shape' Pos'} 
    : Free Shape' Pos' (nat * nat) :=
    impure (injS sget) (fun p => pure (injP p)).

    Definition Put (n : nat * nat) {Shape' : Type} {Pos' : Shape' -> Type} 
    `{Injectable Shape Pos Shape' Pos'} 
    : Free Shape' Pos' unit :=
    impure (injS (sput n)) (fun _ => pure tt).

    Definition BeginShare (n : nat * nat) {Shape' : Type} {Pos' : Shape' -> Type} 
    `{Injectable Shape Pos Shape' Pos'} 
    : Free Shape' Pos' unit :=
    impure (injS (sbsharing n)) (fun _ => pure tt).

    Definition EndShare (n : nat * nat) {Shape' : Type} {Pos' : Shape' -> Type} 
    `{Injectable Shape Pos Shape' Pos'} 
    : Free Shape' Pos' unit :=
    impure (injS (sesharing n)) (fun _ => pure tt).
  End Monad.
End Share.

Export Share.Monad.
