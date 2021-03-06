From Base Require Import Free.
From Base Require Import Free.Instance.Identity.

Require Import Coq.Program.Equality.

Section SecList.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).

  Local Unset Elimination Schemes.
  Inductive List (A : Type) : Type :=
    | nil  : List A
    | cons : Free' A -> Free' (List A) -> List A.
  Local Set Elimination Schemes.

End SecList.

(* smart constructors *)

Notation "'Nil' Shape Pos" :=
  (@pure Shape Pos (List Shape Pos _) (@nil Shape Pos _))
  ( at level 10, Shape, Pos at level 9 ).

Notation "'@Nil' Shape Pos A" :=
  (@pure Shape Pos (List Shape Pos A) (@nil Shape Pos A))
  ( only parsing, at level 10, Shape, Pos, A at level 9 ).

Notation "'Cons' Shape Pos x xs" :=
  (@pure Shape Pos (List Shape Pos _) (@cons Shape Pos _ x xs))
  ( at level 10, Shape, Pos, x, xs at level 9 ).

Notation "'@Cons' Shape Pos A x xs" :=
  (@pure Shape Pos (List Shape Pos A) (@cons Shape Pos A x xs))
  ( only parsing, at level 10, Shape, Pos, A, x, xs at level 9 ).

Arguments nil  {Shape} {Pos} {A}.
Arguments cons {Shape} {Pos} {A}.

(* Normalform instance for lists *)

Section SecListNF.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Variable A : Type.

  Fixpoint nf'List  `{Normalform Shape Pos A}
                     (l : List Shape Pos A)
    : Free Shape Pos (List Identity.Shape Identity.Pos nType)
   := match l with
       | nil => pure nil
       | cons fx fxs => nf fx >>= fun nx =>
                        fxs >>= fun xs =>
                        nf'List xs >>= fun nxs =>
                        pure (cons (pure nx)
                                   (pure nxs))
       end.

  Global Instance NormalformList `{Normalform Shape Pos A}
    : Normalform Shape Pos (List Shape Pos A)
   := { nf' := nf'List }.


End SecListNF.


Section SecListShrArgs.

Variable Shape : Type.
Variable Pos : Shape -> Type.
Variable A : Type.
Context `{ShareableArgs Shape Pos A}.

Fixpoint shareArgsList (S : Strategy Shape Pos) (xs : List Shape Pos A) {struct xs}
  : Free Shape Pos (List Shape Pos A)
 := match xs with
    | nil         => pure nil
    | cons fy fys => share Shape Pos S fy >>= fun sy =>
                     shareWith Shape Pos S shareArgsList fys >>= fun sys =>
                     pure (cons sy sys)
    end.

Global Instance ShareableArgsList
  : ShareableArgs Shape Pos (List Shape Pos A)
 := { shareArgs := shareArgsList }.

End SecListShrArgs.

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

  Fixpoint List_ind (l : List Shape Pos A) : P l.
  Proof.
    destruct l.
    - apply nilP.
    - apply consP.
      apply (ForFree_forall Shape Pos). intros xs HIn.
      induction f0.
      + inversion HIn; subst. apply List_ind.
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
