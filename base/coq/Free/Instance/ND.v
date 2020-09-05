 (** * Definition of the non-determinism effect in terms of the free monad. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Instance.Share.
From Base Require Import Free.Util.Search.
From Base Require Import Free.Util.Sharing.
From Base Require Import Free.Util.Void.

Module ND.
  (* Shape and position function *)
  Inductive Shape : Type :=
  | sfail : Shape
  | schoice : option ID -> Shape.

  Definition Pos (s : Shape) : Type :=
  match s with
  | sfail => Void
  | schoice _ => bool
  end.

  (* Type synonym and smart constructors for the non-determinism effect. *)
  Module Import Monad.
    Definition ND (A : Type) : Type := Free Shape Pos A.

    Definition Fail {A : Type} (Shape' : Type) (Pos' : Shape' -> Type)
      `{Injectable Shape Pos Shape' Pos'}
      : Free Shape' Pos' A :=
      impure (injS sfail) (fun p => (fun (x : Void) => match x with end) (injP p)).

    Definition Choice_ {A : Type} (Shape' : Type) (Pos' : Shape' -> Type)
    `{Injectable Shape Pos Shape' Pos'} mid l r
    : Free Shape' Pos' A :=
       let s := injS (schoice mid)
       in impure s (fun p : Pos' s => if injP p : Pos (schoice mid) then l else r).

    (* Curry notation for the choice operator.
       The ID is set by the sharing handler. *)
    Definition Choice {A} Shape Pos `{I : Injectable ND.Shape ND.Pos Shape Pos} x y
      := @Choice_ A Shape Pos I None x y.
 End Monad.

  (* Handlers for non-determinism and call-time choice. *)
  Module Import Handler.
    (* Helper definitions and handler for non-determinism. *)
    Definition SChoice (Shape' : Type) := Comb.Shape Shape Shape'.
    Definition PChoice {Shape' : Type} (Pos' : Shape' -> Type)
    := Comb.Pos Pos Pos'.

    Fixpoint runChoice {A : Type}
                       {Shape' : Type}
                       {Pos' : Shape' -> Type}
                       (fc : Free (SChoice Shape') (PChoice Pos') A)
     : Free Shape' Pos' (Tree A)
    := match fc with
       | pure x => pure (Leaf x)
       | impure (inl ND.sfail) _ => pure (Empty A)
       | impure (inl (ND.schoice mid)) pf =>
         runChoice (pf true) >>= fun l =>
         runChoice (pf false) >>= fun r =>
         pure (Branch mid l r)
       | impure (inr s) pf =>
         impure s (fun p => runChoice (pf p))
       end.

    (* Helper definitions and handler for sharing combined with non-determinism
       (call-time choice). *)
    Definition SNDShare (Shape' : Type)
    := Comb.Shape Share.Shape (SChoice Shape').
    Definition PNDShare {Shape' : Type} (Pos' : Shape' -> Type)
    := Comb.Pos Share.Pos (PChoice Pos').

    Fixpoint runNDSharing {A : Type}
                          {Shape' : Type}
                          {Pos' : Shape' -> Type}
                          (n : nat * nat)
                          (fs : Free (SNDShare Shape') (PNDShare Pos') A)
     : Free (SChoice Shape') (PChoice Pos') A
    := let fix nameChoices (next : nat)
                           (state : nat * nat)
                           (scope : nat * nat)
                           (scopes : list (nat * nat))
                           (fs : Free (SNDShare Shape') (PNDShare Pos') A)
     : Free (SChoice Shape') (PChoice Pos') A
       := match fs with (* inside scope handler *)
          | pure x => pure x
          | impure (inl (Share.sbsharing n')) pf =>  (* open nested scope *)
             nameChoices 1 state n' (cons n' scopes) (pf tt)
          | impure (inl (Share.sesharing n')) pf =>
             match scopes with
              (* leave nested scope *)
            | cons _ (cons j js) as ks => nameChoices next state j ks (pf tt)
              (* leave outermost scope *)
            | _                        => runNDSharing state (pf tt)
            end
          | impure (inl Share.sget) pf =>
             nameChoices next state scope scopes (pf state) (* get state *)
          | impure (inl (Share.sput n')) pf => (* set new state *)
             nameChoices next n' scope scopes (pf tt)
          | impure (inr (inl (ND.schoice id))) pf => (* mark the scope of a choice *)
            ( let l := nameChoices (next + 1) state scope scopes (pf true) in
             let r := nameChoices (next + 1) state scope scopes (pf false) in
             Choice_ (SChoice Shape') (PChoice Pos') (Some (tripl scope next)) l r)
          | impure (inr (inl ND.sfail)) _ => Fail (SChoice Shape') (PChoice Pos')
          | impure (inr (inr s)) pf => (* other effect *)
             impure (inr s) (fun p => nameChoices next state scope scopes (pf p))
          end
       in match fs with (* outside scope handler *)
          | pure x => pure x
          | impure (inl (Share.sbsharing n'))  pf => (* enter sharing scope *)
            nameChoices 1 n n' (cons n' nil) (pf tt)
          | impure (inl (Share.sesharing n'))  pf => (* error *)
            (runNDSharing n (pf tt))
          | impure (inl Share.sget) pf => (* get state *)
            runNDSharing n (pf n)
          | impure (inl (Share.sput n')) pf => (* set new state *)
            (runNDSharing n' (pf tt))
          | impure (inr s) pf => impure s (fun p => runNDSharing n (pf p)) (* other effect *)
          end.

  End Handler.

  (* Partial instance for the non-determinism effect. *)
  Instance Partial (Shape' : Type) (Pos' : Shape' -> Type)
                   `{Injectable Shape Pos Shape' Pos'}
    : Partial Shape' Pos' := {
      undefined := fun {A : Type}                => Fail Shape' Pos';
      error     := fun {A : Type} (msg : string) => Fail Shape' Pos'
    }.
End ND.


(* The type, smart constructors and handlers should be visible to other modules
   but to use the shape, position function or partial instance the
   identifier must be fully qualified, e.g. [ND.Partial]. *)
Export ND.Handler.
Export ND.Monad.
