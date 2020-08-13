From Base Require Import Free.
From Base Require Import Free.Instance.Identity.

Require Import Coq.Program.Equality.

Section SecList.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).

  Inductive List (A : Type) : Type :=
    | nil  : List A
    | cons : Free' A -> Free' (List A) -> List A.

  Arguments nil  {A}.
  Arguments cons {A}.

  (* smart constructors *)

  Definition Nil {A : Type} : Free' (List A) := pure nil.

  Definition Cons {A : Type} (x : Free' A) (xs : Free' (List A))
    : Free' (List A) :=
    pure (cons x xs).

End SecList.

Arguments nil  {Shape} {Pos} {A}.
Arguments cons {Shape} {Pos} {A}.

(* Normalform instance *)

Fixpoint nf'List (Shape : Type) (Pos : Shape -> Type)
                   (A B : Type) 
                   `{Normalform Shape Pos A B}
                   (l : List Shape Pos A)
  : Free Shape Pos (List Identity.Shape Identity.Pos B)
 := match l with
     | nil => pure nil
     | cons fx fxs => nf fx >>= fun nx =>
                      fxs >>= fun xs =>
                      nf'List Shape Pos A B xs >>= fun nxs =>
                      pure (cons (pure nx) (pure nxs))
     end.

Definition nfList (Shape : Type) (Pos : Shape -> Type)
                  (A B : Type)
                  `{Normalform Shape Pos A B}
                  (p : Free Shape Pos (List Shape Pos A))
  : Free Shape Pos (List Identity.Shape Identity.Pos B)
 := p >>= (fun p' => nf'List Shape Pos A B p').

Lemma nf_impure_list (Shape : Type) (Pos : Shape -> Type)
                     (A B : Type)
                     `{Normalform Shape Pos A B}
  : forall s (pf : _ -> Free Shape Pos (List Shape Pos A)),
    nfList Shape Pos A B (impure s pf) 
    = impure s (fun p => nfList Shape Pos A B (pf p)).
Proof. trivial. Qed.

Lemma nf_pure_list (Shape : Type) (Pos : Shape -> Type)
                   (A B : Type)
                   `{Normalform Shape Pos A B}
  : forall (x : List Shape Pos A),
    nfList Shape Pos A B (pure x) = nf'List Shape Pos A B x.
Proof. trivial. Qed.

Instance NormalformList {Shape : Type} {Pos : Shape -> Type} (A B : Type)
                        `{Normalform Shape Pos A B}
  : Normalform (List Shape Pos A) 
                         (List Identity.Shape Identity.Pos B)
 := {
      nf := nfList Shape Pos A B;
      nf_impure := nf_impure_list Shape Pos A B;
      nf' := nf'List Shape Pos A B;
      nf_pure := nf_pure_list Shape Pos A B
    }.

(* Induction principle for lists *)

Section SecListInd.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Variable A : Type.
  Variable P : List Shape Pos A -> Prop.

  Hypothesis nilP : P nil.

  Hypothesis consP : forall (fx: Free Shape Pos A)
                            (fxs : Free Shape Pos (List Shape Pos A)),
      ForFree Shape Pos (List Shape Pos A) P fxs -> P (cons fx fxs).

  Fixpoint List_Ind (l : List Shape Pos A) : P l.
  Proof.
    destruct l.
    - apply nilP.
    - apply consP.
      apply (ForFree_forall Shape Pos). intros xs HIn.
      induction f0 using Free_Ind.
      + inversion HIn; subst. apply List_Ind.
      + dependent destruction HIn; subst. destruct H0 as [ p ].
        apply H with (p := p). apply H0.
  Defined.

End SecListInd.

(* Induction principle for lists inside the Free monad. *)

Section SecFreeListRect.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable A : Type.
  Variable PF : Free Shape Pos (List Shape Pos A) -> Type.
  Variable P : List Shape Pos A -> Type.

  Hypothesis NilFP : P nil.
  Hypothesis ConsFP : forall fx fxs, PF fxs -> P (cons fx fxs).
  Hypothesis PureListF : forall xs, P xs -> PF (pure xs).
  Hypothesis ImpureP :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (List Shape Pos A)),
    (forall p, PF (pf p)) -> PF (impure s pf).

  Fixpoint List_Rect (xs: List Shape Pos A) : P xs :=
    let fix aux (fys: Free Shape Pos (List Shape Pos A)) : PF fys :=
        match fys with
        | pure ys => PureListF ys (List_Rect ys)
        | impure s pf => ImpureP s pf (fun p => aux (pf p))
        end
    in match xs with
       | nil => NilFP
       | cons fx fxs => ConsFP fx fxs (aux fxs)
       end.

  Fixpoint FreeList_rect (fxs: Free Shape Pos (List Shape Pos A)) : PF fxs :=
    match fxs with
    | pure xs => PureListF xs (List_Rect xs)
    | impure s pf => ImpureP s pf (fun p => FreeList_rect (pf p))
    end.

End SecFreeListRect.

Section SecFreeListInd.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable A : Type.
  Variable PF : Free Shape Pos (List Shape Pos A) -> Type.
  Variable P : List Shape Pos A -> Type.

  Hypothesis NilFP : P nil.
  Hypothesis ConsFP : forall fx fxs, PF fxs -> P (cons fx fxs).
  Hypothesis PureListF : forall xs, P xs -> PF (pure xs).
  Hypothesis ImpureP : forall (s : Shape) (pf : Pos s -> Free Shape Pos (List Shape Pos A)),
      (forall p, PF (pf p)) -> PF (impure s pf).

  Definition FreeList_ind (fxs: Free Shape Pos (List Shape Pos A)) : PF fxs :=
    FreeList_rect Shape Pos A PF P NilFP ConsFP PureListF ImpureP fxs.

End SecFreeListInd.
