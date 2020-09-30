(* Induction principle for the Free monad. *)

From Base Require Import Free.Monad.

Section SecFreeRect.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable A : Type.
  Variable P : Free Shape Pos A -> Type.

  Variable Pure_rect : forall (x : A), P (pure x).
  Variable Impure_rect : forall (s : Shape) (pf : Pos s -> Free Shape Pos A),
      (forall p, P (pf p)) -> P (impure s pf).

  Fixpoint Free_rect (fx : Free Shape Pos A) : P fx :=
    match fx with
    | pure x => Pure_rect x
    | impure s pf =>
      Impure_rect s pf (fun p : Pos s => Free_rect (pf p))
    end.

End SecFreeRect.

Section SecFreeInd.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable A : Type.
  Variable P : Free Shape Pos A -> Type.

  Variable Pure_ind : forall (x : A), P (pure x).
  Variable Impure_ind : forall (s : Shape) (pf : Pos s -> Free Shape Pos A),
      (forall p, P (pf p)) -> P (impure s pf).

  Definition Free_ind (fx : Free Shape Pos A) : P fx
    := Free_rect Shape Pos A P Pure_ind Impure_ind fx.

End SecFreeInd.
