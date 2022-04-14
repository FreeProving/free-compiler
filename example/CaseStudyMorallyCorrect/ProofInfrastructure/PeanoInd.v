From Base Require Import Free.
From Generated Require Import FastLooseBasic.

Require Import Coq.Program.Equality.

Arguments zero  {Shape} {Pos}.
Arguments s {Shape} {Pos} _.

(* Induction principle for peanos *)

Section PeanoInd.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Variable P : Peano Shape Pos -> Prop.

  Hypothesis zeroP : P zero.

  Hypothesis sP : forall (fx : Free Shape Pos (Peano Shape Pos)),
      ForFree Shape Pos (Peano Shape Pos) P fx -> P (s fx).

  Fixpoint Peano_Ind (p : Peano Shape Pos) : P p.
  Proof.
    destruct p.
    - apply zeroP.
    - apply sP.
      apply (ForFree_forall Shape Pos). intros x HIn.
      induction f using Free_Ind.
      + inversion HIn; subst. apply Peano_Ind.
      + dependent destruction HIn; subst. destruct H0 as [ p ].
        apply H with (p := p). apply H0.
  Defined.

End PeanoInd.

(* Induction principle for peanos inside the Free monad. *)

Section FreePeanoRect.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable PF : Free Shape Pos (Peano Shape Pos) -> Type.
  Variable P : Peano Shape Pos -> Type.

  Hypothesis ZeroFP : P zero.
  Hypothesis SFP : forall fx, PF fx -> P (s fx).
  Hypothesis PurePeanoF : forall xs, P xs -> PF (pure xs).
  Hypothesis ImpureP :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Peano Shape Pos)),
    (forall p, PF (pf p)) -> PF (impure s pf).

  Fixpoint Peano_Rect (x: Peano Shape Pos) : P x :=
    let fix aux (fx: Free Shape Pos (Peano Shape Pos)) : PF fx :=
        match fx with
        | pure x => PurePeanoF x (Peano_Rect x)
        | impure sh pf => ImpureP sh pf (fun p => aux (pf p))
        end
    in match x with
       | zero => ZeroFP
       | s fx => SFP fx (aux fx)
       end.

  Fixpoint FreePeano_rect (fx: Free Shape Pos (Peano Shape Pos)) : PF fx :=
    match fx with
    | pure x => PurePeanoF x (Peano_Rect x)
    | impure sh pf => ImpureP sh pf (fun p => FreePeano_rect (pf p))
    end.

End FreePeanoRect.

Section FreePeanoInd.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable PF : Free Shape Pos (Peano Shape Pos) -> Type.
  Variable P : Peano Shape Pos -> Type.

  Hypothesis ZeroFP : P zero.
  Hypothesis SFP : forall fx, PF fx -> P (s fx).
  Hypothesis PurePeanoF : forall xs, P xs -> PF (pure xs).
  Hypothesis ImpureP :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Peano Shape Pos)),
    (forall p, PF (pf p)) -> PF (impure s pf).


  Definition FreePeano_ind (fx: Free Shape Pos (Peano Shape Pos)) : PF fx :=
    FreePeano_rect Shape Pos PF P ZeroFP SFP PurePeanoF ImpureP fx.

End FreePeanoInd.
