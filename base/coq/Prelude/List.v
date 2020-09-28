From Base Require Import Free.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Malias.

Require Import Coq.Program.Equality.

Section SecList.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).

  Unset Elimination Schemes.
  Inductive List (A : Type) : Type :=
    | nil  : List A
    | cons : Free' A -> Free' (List A) -> List A.
  Set Elimination Schemes.

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

Fixpoint shareArgsList `{SA : ShareableArgs Shape Pos A}
                       `{Injectable Share.Shape Share.Pos Shape Pos}
                        (xs : List Shape Pos A)
                        {struct xs}
  : Free Shape Pos (List Shape Pos A)
 := match xs with
    | nil         => pure nil
    | cons fy fys => cbneed Shape Pos (@shareArgs Shape Pos A SA) fy >>= fun sy =>
                     cbneed Shape Pos shareArgsList fys >>= fun sys =>
                     pure (cons sy sys)
                         end.

Global Instance ShareableArgsList `{Injectable Share.Shape Share.Pos Shape Pos}
                           `{ShareableArgs Shape Pos A}
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
      induction f0 using Free_Ind.
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

(* [ForList] property to generate induction hypotheses over lists. *)
Inductive ForList (Shape : Type) (Pos : Shape -> Type) (a : Type) (P0 : a -> Prop)
   : List Shape Pos a -> Prop
  := ForList_nil : ForList Shape Pos a P0 (@nil Shape Pos a)
  |  ForList_cons
   : forall (x : Free Shape Pos a) (x0 : Free Shape Pos (List Shape Pos a)),
     ForFree Shape Pos a P0 x ->
     ForFree Shape Pos (List Shape Pos a) (ForList Shape Pos a P0) x0 ->
     ForList Shape Pos a P0 (@cons Shape Pos a x x0).

Inductive InList (Shape : Type) (Pos : Shape -> Type) (a : Type)
   : a -> List Shape Pos a -> Prop
  := InList_cons
   : forall (x1 : a)
     (x : Free Shape Pos a)
     (x0 : Free Shape Pos (List Shape Pos a)),
     InFree Shape Pos a x1 x -> InList Shape Pos a x1 (@cons Shape Pos a x x0)
  |  InList_cons0
   : forall (x1 : a)
     (x2 : List Shape Pos a)
     (x : Free Shape Pos a)
     (x0 : Free Shape Pos (List Shape Pos a)),
     InList Shape Pos a x1 x2 ->
     InFree Shape Pos (List Shape Pos a) x2 x0 ->
     InList Shape Pos a x1 (@cons Shape Pos a x x0).


(* 'Forall' lemma to rewrite [ForList] properties. *)
Lemma ForList_forall : forall (Shape : Type)
  (Pos : Shape -> Type)
  (a : Type)
  (P0 : a -> Prop)
  (x : List Shape Pos a),
  ForList Shape Pos a P0 x <->
  (forall (y : a), InList Shape Pos a y x -> P0 y).
Proof.
  intros Shape Pos a P0.
  Local Hint Extern 1 => prove_forall_finish_rtl InList_cons : prove_forall_db.
  Local Hint Extern 1 => prove_forall_finish_rtl InList_cons0 : prove_forall_db.
  prove_forall List_ind.
Defined.

(* Add hints for proof generation. *)
Hint Extern 0 (ForList _ _ _ _ ?x) =>
  prove_ind_prove_ForType x ForList_forall List_ind : prove_ind_db.
Hint Extern 0 =>
  match goal with
  | [ HF : ForList ?Shape ?Pos ?T _ ?fx
    , HI : InList ?Shape ?Pos ?T ?x ?fx
    |- _ ] =>
      prove_forall_ForType_InType HF HI x ForList_forall
  end : prove_forall_db.
Hint Extern 0 (ForList _ _ _ _ _) =>
  prove_forall_prove_ForType ForList_forall : prove_forall_db.
