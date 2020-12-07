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
  Section SecShareHandler.
    Context {Shape' : Type}.
    Context {Pos'   : Shape' -> Type}.
    Context {A      : Type}.

    Notation "'FreeComb'" := (Free (Comb.Shape Shape Shape') (Comb.Pos Pos Pos')).
    Notation "'Free''"    := (Free Shape' Pos').

    Fixpoint runEmptySharing (n : nat * nat) (fs : FreeComb A) 
      : Free Shape' Pos' A
     := match fs with (* outside scope handler *)
        | pure x => pure x
        | impure (inl (Share.sbsharing n')) pf =>
            (* enter sharing scope *)
            runInnerScope 1 n n' (cons n' nil) (pf tt)
        | impure (inl (Share.sesharing n')) pf =>
            (* error *)
            runEmptySharing n (pf tt)
        | impure (inl Share.sget) pf =>
            (* get state *)
            runEmptySharing n (pf n)
        | impure (inl (Share.sput n')) pf =>
            (* set new state *)
            runEmptySharing n' (pf tt)
        | impure (inr s) pf =>
            (* other effect *)
            impure s (fun p => runEmptySharing n (pf p))
        end
    with runInnerScope (next : nat)
                       (state : nat * nat)
                       (scope : nat * nat)
                       (scopes : list (nat * nat))
                       (fs : FreeComb A)
      : Free' A
     := match fs with (* inside scope handler *)
        | pure x => pure x
        | impure (inl (Share.sbsharing n')) pf =>
           (* open nested scope *)
           runInnerScope 1 state n' (cons n' scopes) (pf tt)
        | impure (inl (Share.sesharing n')) pf =>
           match scopes with
           | cons _ (cons j js) as ks =>
               (* leave nested scope *)
               runInnerScope next state j ks (pf tt)
           | _                        =>
               (* leave outermost scope *)
               runEmptySharing state (pf tt)
          end
        | impure (inl Share.sget) pf =>
            (* get state *)
            runInnerScope next state scope scopes (pf state)
        | impure (inl (Share.sput n')) pf =>
            (* set new state *)
            runInnerScope next n' scope scopes (pf tt)
        | impure (inr s) pf =>
           (* other effect *)
           impure s (fun p => runInnerScope next state scope scopes (pf p))
        end.
  End SecShareHandler.
  End Handler.
End Share.

Export Share.Handler.
Export Share.Monad.
