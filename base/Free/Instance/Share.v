(** * Definition of the state effect in terms of the free monad. *)

From Base Require Import Free.

Module Share.

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

  (* Type synonym and smart constructors for the state monad. *)
  Module Import Monad.
    Definition Share (A : Type) : Type := Free Shape Pos A.
    
    Definition Get : Share (nat * nat) :=
    impure sget pure.

    Definition Put (n : nat * nat) : Share unit :=
    impure (sput n) (fun _ => pure tt).

    Definition BeginShare (n : nat * nat) : Share unit :=
    impure (sbsharing n) (fun _ => pure tt).

    Definition EndShare (n : nat * nat) : Share unit :=
    impure (sesharing n) (fun _ => pure tt).
  End Monad.
End Share.

Export Share.Monad.
