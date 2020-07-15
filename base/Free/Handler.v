(** Handlers for non-determinism, sharing of non-determnistic values and 
    Maybe, as well as a handler for an effect-free program *)

From Base Require Import Free.
From Base Require Export Instance.Comb.
From Base Require Export Instance.Identity.
From Base Require Export Instance.Maybe.
From Base Require Export Instance.ND.
From Base Require Export Instance.Share.
From Base Require Export Instance.Trace.
From Base Require Import Util.Search.

Set Implicit Arguments.

(* Handler for an effect-free program *)
Definition run A (fz : Free Identity.Shape Identity.Pos A) : A :=
  match fz with 
  | pure x => x
  | impure s _ => match s with end
  end.

(* Handler for a program containing Maybe *)

Definition SMaybe {Shape : Type} := Comb.Shape Maybe.Shape Shape.
Definition PMaybe {Shape : Type} {Pos : Shape -> Type} := Comb.Pos Maybe.Pos Pos.

Fixpoint runMaybe A {Shape : Type} {Pos : Shape -> Type} 
  (fm : Free SMaybe PMaybe A) 
  : Free Shape Pos (option A) :=
  match fm with 
  | pure x            => pure (Some x)
  | impure (inl s) _  => pure None
  | impure (inr s) pf => impure s (fun p : Pos s => runMaybe (pf p))
  end.

(* Handler for a non-deterministic program *)

Definition SChoice {Shape : Type} := Comb.Shape ND.Shape Shape.
Definition PChoice {Shape : Type} {Pos : Shape -> Type} := Comb.Pos ND.Pos Pos.

Fixpoint runChoice A {Shape : Type} {Pos : Shape -> Type} 
  (fc : Free SChoice PChoice A) 
  : Free Shape Pos (Tree A) :=
  match fc with
  | pure x                           => 
      pure (Leaf x)

  | impure (inl ND.sfail) _          => 
      pure (Empty A)

  | impure (inl (ND.schoice mid)) pf =>
      runChoice (pf true) >>= fun l  =>
      runChoice (pf false) >>= fun r =>
      pure (Branch mid l r)

  | impure (inr s) pf                =>
      impure s (fun p : Pos s => runChoice (pf p))
  end.

(* Handler for a program containing tracing *)

Definition ID : Type := nat * nat * nat.
Definition STrace {Shape : Type} := Comb.Shape Trace.Shape Shape.
Definition PTrace {Shape : Type} {Pos : Shape -> Type} := 
  Comb.Pos Trace.Pos Pos.

Fixpoint runTracing A {Shape : Type} {Pos : Shape -> Type} 
  (fm : Free STrace PTrace A) 
  : Free Shape Pos (A * list (option ID * string)) :=
  match fm with 
  | pure x => pure (x,nil)
  | impure (inl s) pf => runTracing (pf tt) >>= fun pair => match pair with
            | (x,msgs)     => pure (x,cons s msgs) 
            end
  | impure (inr s) pf => impure s (fun p : Pos s => runTracing (pf p))
  end.

(* Sharing handlers *)

(* Helper function to construct a triple from a pair and a single value *)
Definition tripl A B C (p : A * B) (c : C) : A * B * C :=
  let '(a,b) := p in (a,b,c). 

(* Handler for sharing combined with non-determinism (call-time choice) *)

Definition SNDShare {Shape : Type} := 
  Comb.Shape Share.Shape (Comb.Shape ND.Shape Shape).
Definition PNDShare {Shape : Type} {Pos : Shape -> Type} := 
  Comb.Pos Share.Pos (Comb.Pos ND.Pos Pos).

Fixpoint runNDSharing A {Shape : Type} {Pos : Shape -> Type} 
  (n : nat * nat)
  (fs : Free SNDShare PNDShare A) 
  : Free (@SChoice Shape) (@PChoice Shape Pos) A :=
  let fix nameChoices (next : nat) (scope : nat * nat) (scopes : list (nat * nat)) 
  (fs : Free SNDShare PNDShare A)
  : Free SChoice PChoice A  :=
      match fs with (* inside scope handler *)
      | pure x                                =>
          pure x
      | impure (inl (Share.sbsharing n')) pf  =>
        nameChoices 1 n' (cons n' scopes) (pf tt)
      | impure (inl (Share.sesharing n')) pf  =>
        match scopes with
        | cons _ (cons j js) as ks => nameChoices next j ks (pf tt)
        | _                        => runNDSharing scope (pf tt)
        end
      | impure (inl Share.sget) pf            =>
          nameChoices next scope scopes (pf n)
      | impure (inl (Share.sput n')) pf       =>
          nameChoices next n' scopes (pf tt)
      | impure (inr (inl (ND.schoice id))) pf =>
              let l := nameChoices (next + 1) scope scopes (pf true) in
              let r := nameChoices (next + 1) scope scopes (pf false) in
              Choice (Some (tripl scope next)) l r
      | impure (inr (inl ND.sfail)) _         =>
          Fail
      | impure (inr (inr s)) pf               =>
          impure (inr s) (fun p => nameChoices next scope scopes (pf p))
      end
  in match fs with (* outside scope handler *)
     | pure x => pure x
     | impure (inl (Share.sbsharing n'))  pf =>
       nameChoices 1 n' (cons n' nil) (pf tt)
     | impure (inl (Share.sesharing n'))  pf =>
         runNDSharing n' (pf tt) (* error *)
     | impure (inl Share.sget) pf =>
         runNDSharing n (pf n)
     | impure (inl (Share.sput n')) pf =>
         runNDSharing n' (pf tt)
     | impure (inr s) pf => impure s (fun p =>
         runNDSharing n (pf p))
     end.

(* Handler for sharing combined with non-determinism (call-time choice) *)
Fixpoint runTraceSharing A {Shape : Type} {Pos : Shape -> Type} 
  (n : nat * nat)
  (fs : Free (Comb.Shape Share.Shape (Comb.Shape Trace.Shape Shape))
  (Comb.Pos Share.Pos (Comb.Pos Trace.Pos Pos)) A)
  : Free (Comb.Shape Trace.Shape Shape) (Comb.Pos Trace.Pos Pos) A :=
  let fix nameMessages (next : nat) (scope : nat * nat)
  (scopes : list (nat * nat))
  (fs : Free (Comb.Shape Share.Shape (Comb.Shape Trace.Shape Shape))
  (Comb.Pos Share.Pos (Comb.Pos Trace.Pos Pos)) A)
  : Free (Comb.Shape Trace.Shape Shape) (Comb.Pos Trace.Pos Pos) A  :=
      match fs with (* inside scope handler *)
      | pure x                               => pure x
      | impure (inl (Share.sbsharing n')) pf =>
        nameMessages 1 n' (cons n' scopes) (pf tt)
      | impure (inl (Share.sesharing n')) pf =>
        match scopes with
        | cons _ (cons j js) as ks => nameMessages next j ks (pf tt)
        | _                        => runTraceSharing scope (pf tt)
        end
      | impure (inl Share.sget) pf           =>
          nameMessages next scope scopes (pf n)
      | impure (inl (Share.sput n')) pf      =>
          nameMessages next n' scopes (pf tt)
      | impure (inr (inl (_,msg))) pf        =>
          let x := nameMessages (next + 1) scope scopes (pf tt) in
          LCons (Some (tripl scope next)) msg x
      | impure (inr (inr s)) pf              =>
          impure (inr s) (fun p => nameMessages next scope scopes (pf p)) 
      end
  in match fs with (* outside scope handler *)
     | pure x => pure x
     | impure (inl (Share.sbsharing n'))  pf =>
       nameMessages 1 n' (cons n' nil) (pf tt)
     | impure (inl (Share.sesharing n'))  pf =>
         runTraceSharing n' (pf tt) (* error *)
     | impure (inl Share.sget) pf            =>
         runTraceSharing n (pf n)
     | impure (inl (Share.sput n')) pf       =>
         runTraceSharing n' (pf tt)
     | impure (inr s) pf                     =>
         impure s (fun p => runTraceSharing n (pf p))
     end.
