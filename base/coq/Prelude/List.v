From Base Require Import Free.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Malias.

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

(* Normalform instance for lists *)

Section SecListNF.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Variable A B : Type. 

  Fixpoint nf'List  `{Normalform Shape Pos A B}
                     (l : List Shape Pos A)
    : Free Shape Pos (List Identity.Shape Identity.Pos B)
   := match l with
       | nil => pure nil
       | cons fx fxs => nf fx >>= fun nx =>
                        fxs >>= fun xs =>
                        nf'List xs >>= fun nxs =>
                        pure (cons (pure nx) (pure nxs))
       end.

  Global Instance NormalformList `{Normalform Shape Pos A B}
    : Normalform Shape Pos (List Shape Pos A) 
                           (List Identity.Shape Identity.Pos B)
   := { nf' := nf'List }.

End SecListNF.

Section SecListShrArgs.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable A : Type.

  Fixpoint shareArgsList `{ShareableArgs Shape Pos A}
                         `{Injectable Share.Shape Share.Pos Shape Pos}
                          (xs : List Shape Pos A)
    : Free Shape Pos (List Shape Pos A)
   := 
                         let shr fp := Get Shape Pos >>= fun '(i,j) =>
                                       Put Shape Pos (i + 1, j) >>
                                       pure (BeginShare Shape Pos (i,j) >>
                                             Put Shape Pos (i, j + 1) >>
                                             fp >>= fun x =>
                                             shareArgsList x >>= fun x' =>
                                             Put Shape Pos (i + 1, j) >>
                                             EndShare Shape Pos (i,j) >>
                                             pure x')
                         in
                         match xs with
                         | nil         => pure nil
                         | cons fy fys => 
                                          shr fys >>= fun sys => 
                                          cbneed Shape Pos fy >>= fun sy => 
                                          pure (cons sy sys)
                         end.

Global Instance ShareableArgsList `{Injectable Share.Shape Share.Pos Shape Pos}
                           `{ShareableArgs Shape Pos A}
  : ShareableArgs Shape Pos (List Shape Pos A)
 := {
        shareArgs := shareArgsList
    }.

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
