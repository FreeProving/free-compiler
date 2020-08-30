(** * Definition of the sharing effect in terms of the free monad. *)

From Base Require Import Free.Class.Injectable.
From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Monad.

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

  (* Sharing handler for effects that do not require sharing. *)
  Module Import Handler.

    Fixpoint runEmptySharing {A : Type} 
                          {Shape' : Type} 
                          {Pos' : Shape' -> Type}
                          (n : nat * nat)
                          (fs : Free (Comb.Shape Shape Shape') (Comb.Pos Pos Pos') A) 
     : Free Shape' Pos' A 
    := let fix runInnerScope (next : nat)
                           (state : nat * nat)
                           (scope : nat * nat) 
                           (scopes : list (nat * nat)) 
                           (fs : Free (Comb.Shape Shape Shape') (Comb.Pos Pos Pos') A)
     : Free Shape' Pos' A
       := match fs with (* inside scope handler *)
          | pure x => pure x
          | impure (inl (Share.sbsharing n')) pf =>  (* open nested scope *)
             runInnerScope 1 state n' (cons n' scopes) (pf tt)
          | impure (inl (Share.sesharing n')) pf => 
             match scopes with
              (* leave nested scope *)
            | cons _ (cons j js) as ks => runInnerScope next state j ks (pf tt)
              (* leave outermost scope *)
            | _                        => runEmptySharing state (pf tt)
            end
          | impure (inl Share.sget) pf => 
             runInnerScope next state scope scopes (pf state) (* get state *)
          | impure (inl (Share.sput n')) pf => (* set new state *)
             runInnerScope next n' scope scopes (pf tt)
          | impure (inr s) pf => (* other effect *)
             impure s (fun p => runInnerScope next state scope scopes (pf p))
          end
       in match fs with (* outside scope handler *)
          | pure x => pure x
          | impure (inl (Share.sbsharing n'))  pf => (* enter sharing scope *)
            runInnerScope 1 n n' (cons n' nil) (pf tt)
          | impure (inl (Share.sesharing n'))  pf => (* error *)
            (runEmptySharing n (pf tt))
          | impure (inl Share.sget) pf => (* get state *)
            runEmptySharing n (pf n)
          | impure (inl (Share.sput n')) pf => (* set new state *)
            (runEmptySharing n' (pf tt))
          | impure (inr s) pf => impure s (fun p => runEmptySharing n (pf p)) (* other effect *)
          end.

  End Handler.
End Share.

Export Share.Handler.
Export Share.Monad.
