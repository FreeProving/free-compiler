From Base Require Import Free Prelude.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

From Examples Require Import Queue.Props.
From Examples Require Import Queue.Queue.
From Examples Require Import Queue.QueueI.
From Examples Require Import Queue.Util.

(* TODO: Can we generate generate total_* properties? *)

Inductive total_list (Shape : Type) (Pos : Shape -> Type) {a : Type}
    (total_a : Free Shape Pos a -> Prop)
  : Free Shape Pos (List Shape Pos a) -> Prop :=
  | total_nil : total_list Shape Pos total_a (pure nil)
  | total_cons : forall (fx : Free Shape Pos a)
                        (fxs : Free Shape Pos (List Shape Pos a)),
                 total_a fx
                 -> total_list Shape Pos total_a fxs
                 -> total_list Shape Pos total_a (Cons Shape Pos fx fxs).

Inductive total_pair (Shape : Type) (Pos : Shape -> Type) {a : Type} {b : Type}
    (total_a : Free Shape Pos a -> Prop)
    (total_b : Free Shape Pos b -> Prop)
  : Free Shape Pos (Pair Shape Pos a b) -> Prop :=
  | total_pair_ : forall (fx : Free Shape Pos a)
                         (fy : Free Shape Pos b),
                  total_a fx
                  -> total_b fy
                  -> total_pair Shape Pos total_a total_b (Pair_ Shape Pos fx fy).

Definition total_queue (Shape : Type) (Pos : Shape -> Type) {a : Type}
    (total_a : Free Shape Pos a -> Prop)
  : (Free Shape Pos (QueueI Shape Pos a)) -> Prop :=
  total_pair Shape Pos (total_list Shape Pos total_a)
                       (total_list Shape Pos total_a).

(* Lemmas *)

Lemma is_pure_true_or :
  forall (Shape : Type)
         (Pos : Shape -> Type)
         (fb1 fb2 : Free Shape Pos (Bool Shape Pos)),
  orBool Shape Pos fb1 fb2 = True_ Shape Pos
  -> fb1 = True_ Shape Pos \/ fb2 = True_ Shape Pos.
Proof.
  intros Shape Pos fb1 fb2 Hpure.
  destruct fb1 as [ b1 |], fb2 as [ b2 |]; simpl in *.
  - (* fb1 = pure b1,    fb2 = pure b2 *)    destruct b1; auto.
  - (* fb1 = pure b1,    fb2 = impure _ _ *) destruct b1; auto.
  - (* fb1 = impure _ _, fb2 = pure b2 *)    discriminate Hpure.
  - (* fb1 = impure _ _, fb2 = impure _ _ *) discriminate Hpure.
Qed.

Lemma is_pure_true_and :
  forall (Shape : Type)
         (Pos : Shape -> Type)
         (fb1 fb2 : Free Shape Pos (Bool Shape Pos)),
   andBool Shape Pos fb1 fb2 = True_ Shape Pos
   -> fb1 = True_ Shape Pos /\ fb2 = True_ Shape Pos.
Proof.
  intros Shape Pos fb1 fb2 Hpure.
  destruct fb1 as [ b1 |], fb2 as [ b2 |] ; simpl in *.
  - (* fb1 = pure b1,    fb2 = pure b2 *)    destruct b1, b2; auto.
  - (* fb1 = pure b1,    fb2 = impure _ _ *) destruct b1; discriminate Hpure.
  - (* fb1 = impure _ _, fb2 = pure b2 *)    discriminate Hpure.
  - (* fb1 = impure _ _, fb2 = impure _ _ *) discriminate Hpure.
Qed.

Lemma null_rev :
  forall (Shape : Type)
    (Pos : Shape -> Type)
    {a : Type}
    (fxs : Free Shape Pos (List Shape Pos a)),
    null Shape Pos fxs = True_ Shape Pos
    -> null Shape Pos (reverse Shape Pos fxs) = True_ Shape Pos.
Proof.
  intros Shape Pos a fxs Hnull.
  destruct fxs as [ xs |  ].
  - (* fxs = pure xs *)
    destruct xs.
    + (* xs = nil *) trivial.
    + (* xs = cons _ _ *) discriminate Hnull.
  - (* fxs = impure _ _ *)
    discriminate Hnull.
Qed.

Lemma append_nil:
  forall (Shape : Type)
         (Pos : Shape -> Type)
         (a : Type)
         (fxs : Free Shape Pos (List Shape Pos a)),
  append Shape Pos fxs (pure nil) = fxs.
Proof.
  intros Shape Pos a fxs.
  induction fxs using FreeList_ind with (P := fun xs => append_0 Shape Pos xs (pure nil) = pure xs); simpl.
  - reflexivity.
  - unfold Cons; simpl; repeat apply f_equal. apply IHfxs1.
  - apply IHfxs.
  - repeat apply f_equal. extensionality p. apply H.
Qed.

Lemma append_0_assoc :
  forall (Shape : Type)
         (Pos : Shape -> Type)
         {a : Type}
         (xs : List Shape Pos a)
         (fys fzs : Free Shape Pos (List Shape Pos a)),
      append_0 Shape Pos xs (append Shape Pos fys fzs)
      = append Shape Pos (append_0 Shape Pos xs fys) fzs.
Proof.
  intros Shape Pos a xs fys fzs.
  induction xs using List_Ind.
  - reflexivity.
  - induction fxs using Free_Ind.
    + simpl. simplify H as IH. rewrite IH. reflexivity.
    + (*Inductive case: [fxs = impure s pf] with induction hypothesis [H] *)
      simpl. do 2 apply f_equal. extensionality p.
      simplify H as IH. apply IH.
Qed.

Lemma append_assoc :
  forall (Shape : Type)
         (Pos : Shape -> Type)
         {a : Type}
         (fxs fys fzs : Free Shape Pos (List Shape Pos a)),
    append Shape Pos fxs (append Shape Pos fys fzs)
    = append Shape Pos (append Shape Pos fxs fys) fzs.
Proof.
  intros Shape Pos a fxs fys fzs.
  induction fxs as [ | s pf IH ] using Free_Ind.
  - simpl. apply append_0_assoc.
  - (*Inductive case: [fxs = impure s pf] with induction hypothesis [IH] *)
    simpl. apply f_equal. extensionality p.
    apply IH.
Qed.

Definition singleton (Shape : Type)
                     (Pos : Shape -> Type)
                     {a : Type}
                     (fx : Free Shape Pos a)
  : Free Shape Pos (List Shape Pos a)
  := Cons Shape Pos fx (Nil Shape Pos).

(* QuickCheck properties *)
Theorem prop_isEmpty : forall (Shape : Type)
  (Pos : Shape -> Type)
  {a : Type} (total_a : Free Shape Pos a -> Prop)
  (qi : Free Shape Pos (QueueI Shape Pos a)),
  total_queue Shape Pos total_a qi ->
  (invariant Shape Pos qi = True_ Shape Pos) ->
  (isEmptyI Shape Pos qi = isEmpty Shape Pos (toQueue Shape Pos qi)).
Proof.
  intros Shape Pos a total_a fqi Htotal Hinv.
  destruct fqi as [qi | ].
  - (* fqi = pure qi *)
    destruct qi as [fxs fys]. (* qi = (fxs, fys) *)
    destruct fxs as [xs | ].
    + (* fxs = pure xs *)
      destruct xs as [| fx fxs'].
      * (* xs = Nil *)
        simpl in *. apply (is_pure_true_or Shape Pos) in Hinv.
        destruct Hinv as [Hnull | Hcontra].
        -- (* null Shape Pos fys *)
           apply null_rev in Hnull.
           symmetry. unfold isEmpty. apply Hnull.
        -- (* False_ Shape Pos *)
           discriminate Hcontra.
      * (* xs = Cons fx fxs' *)
        simpl. reflexivity.
    + (* fxs = impure _ _ *)
      inversion Htotal. inversion H1.
  - (* fqi = impure _ _ *)
    inversion Htotal.
Qed.

(* In fact we do not need the totality constraint in this case. *)
Theorem prop_isEmpty' : forall (Shape : Type)
  (Pos : Shape -> Type)
  {a : Type}
  (qi : Free Shape Pos (QueueI Shape Pos a)),
  (invariant Shape Pos qi = True_ Shape Pos) ->
  (isEmptyI Shape Pos qi = isEmpty Shape Pos (toQueue Shape Pos qi)).
Proof.
  intros Shape Pos a fqi Hinv.
  destruct fqi as [qi | ].
  - (* fqi = pure qi *)
    destruct qi as [fxs fys]. (* qi = (fxs, fys) *)
    destruct fxs as [xs | ].
    + (* fxs = pure xs *)
      destruct xs as [| fx fxs'].
      * (* xs = Nil *)
        simpl in *. apply is_pure_true_or in Hinv.
        destruct Hinv as [Hnull | Hcontra].
        -- (* null Shape Pos fys *)
           apply null_rev in Hnull.
           symmetry. unfold isEmpty. apply Hnull.
        -- (* False_ Shape Pos *)
           discriminate Hcontra.
      * (* xs = Cons fx fxs' *)
        simpl. reflexivity.
    + (* fxs = impure _ _ *)
      simpl in *. apply is_pure_true_or in Hinv.
      destruct Hinv as [Hnull | Hcontra].
      -- (* null Shape Pos fys *)
         apply f_equal, functional_extensionality. intros x.
         apply null_rev in Hnull.
         destruct (reverse Shape Pos fys) as [[| y ys'] |].
         ++ (* reverse Shape Pos fys = Nil Shape Pos *)
            rewrite append_nil. unfold isEmpty. reflexivity.
         ++ (* reverse Shape Pos fys = Cons Shape Pos y ys' *)
            simpl in Hnull. discriminate Hnull.
         ++ (* reverse Shape Pos fys = impure _ _*)
            simpl in Hnull. discriminate Hnull.
      -- (* impure _ _ = True_ Shape Pos *)
         discriminate Hcontra.
  - (* fqi = impure _ _ *)
    simpl in Hinv. discriminate Hinv.
Qed.

Theorem prop_add :
  forall
    (Shape : Type)
    (Pos : Shape -> Type)
    {a : Type}
    (x : Free Shape Pos a)
    (qi : Free Shape Pos (QueueI Shape Pos a)),
  toQueue Shape Pos (addI Shape Pos x qi)
  = add Shape Pos x (toQueue Shape Pos qi).
Proof.
  intros Shape Pos a fx fqi.
  induction fqi as [ [f1 f2] | eq ] using Free_Ind; simpl.
  - destruct f1 as [l | s pf]; simpl.
    + destruct l as [ | fy fys]; simpl.
      * rewrite append_nil. reflexivity.
      * apply (append_assoc Shape Pos (pure (cons fy fys)) (reverse Shape Pos f2) (singleton Shape Pos fx)).
    + repeat apply f_equal. extensionality p.
      induction (pf p) as [fys |] using Free_Ind; simpl.
      * destruct fys; simpl.
        -- rewrite append_nil.
           reflexivity.
        -- apply f_equal. apply (append_assoc Shape Pos f0 (reverse Shape Pos f2) (singleton Shape Pos fx)).
      * repeat apply f_equal.
        extensionality p1.
        apply H.
  - repeat apply f_equal.
    extensionality p.
    apply H.
Qed.

(* Version of prop_add if we would generate totality constraints automatically. *)
Theorem prop_add' :
  forall
    (Shape : Type)
    (Pos : Shape -> Type)
    {a : Type} (total_a : Free Shape Pos a -> Prop)
    (x : Free Shape Pos a)
    (qi : Free Shape Pos (QueueI Shape Pos a)),
  total_a x
  -> total_queue Shape Pos total_a qi
  -> toQueue Shape Pos (addI Shape Pos x qi)
     = add Shape Pos x (toQueue Shape Pos qi).
Proof.
  intros Shape Pos a total_a fx fqi HtotalX HtotalQ.
  induction fqi as [ [f1 f2] | eq ] using Free_Ind; simpl.
  - destruct f1 as [l | s pf]; simpl.
    + destruct l as [ | fy fys]; simpl.
      * rewrite append_nil. reflexivity.
      * apply (append_assoc Shape Pos (pure (cons fy fys)) (reverse Shape Pos f2) (singleton Shape Pos fx)).
    + repeat apply f_equal. extensionality p.
      induction (pf p) as [fys |] using Free_Ind; simpl.
      * destruct fys; simpl.
        -- rewrite append_nil.
           reflexivity.
        -- apply f_equal. apply (append_assoc Shape Pos f0 (reverse Shape Pos f2) (singleton Shape Pos fx)).
      * repeat apply f_equal.
        extensionality p1.
        apply H.
  - repeat apply f_equal.
    extensionality p.
    apply H.
    inversion HtotalQ.
Qed.

Theorem prop_front :
  forall (Shape : Type)
         (Pos : Shape -> Type)
         (P : Partial Shape Pos)
         {a : Type} (total_a : Free Shape Pos a -> Prop)
         (qi : Free Shape Pos (QueueI Shape Pos a)),
  total_queue Shape Pos total_a qi
  -> (andBool Shape Pos
        (invariant Shape Pos qi)
        (not Shape Pos (isEmptyI Shape Pos qi))
      = True_ Shape Pos)
  -> (frontI Shape Pos P qi = front Shape Pos P (toQueue Shape Pos qi)).
Proof.
  intros Shape Pos P a total_a fqi Htotal HinvNempty.
  apply is_pure_true_and in HinvNempty.
  destruct HinvNempty as [Hinv Hnempty].
  destruct Htotal as [ff fb Htotal1 Htotal2]. (* fqi = pure (ff, fb) *)
  destruct ff as [f |].
    + (* ff = pure f *)
      destruct f.
      * (* f = nil *) discriminate Hnempty.
      * (* f = cons _ _ *) simpl. reflexivity.
    + inversion Htotal1.
Qed.

Fail Theorem prop_inv_empty : forall (Shape : Type) (Pos : Shape -> Type),
  invariant Shape Pos (emptyI Shape Pos) = True_ Shape Pos.
(*
  The command has indeed failed with message:
  Cannot infer the implicit parameter a of invariant whose type is "Type" in environment:
  Shape : Type
  Pos : Shape -> Type
*)

Theorem prop_inv_empty : forall (Shape : Type) (Pos : Shape -> Type) (a : Type),
  invariant Shape Pos (@emptyI Shape Pos a) = True_ Shape Pos.
Proof.
  intros Shape Pos a.
  simpl. reflexivity.
Qed.

Theorem prop_inv_add : forall (Shape : Type)
  (Pos : Shape -> Type)
  {a : Type}
  (x : Free Shape Pos a)
  (q : Free Shape Pos (QueueI Shape Pos a)),
  (invariant Shape Pos q = True_ Shape Pos) ->
  (invariant Shape Pos (addI Shape Pos x q) = True_ Shape Pos).
Proof.
  intros Shape Pos a fx fq H. destruct fq as [[ff fb] |].
  - (* fq = Pair_ Shape Pos ff fb *)
    destruct ff as [f |]; destruct fb as [b |].
    + (* ff = pure f; fb = pure b *)
      destruct f; reflexivity.
    + (* ff = pure f; fb = impure _ _ *)
      discriminate H.
    + (* ff = impure _ _; fb = pure b *)
      destruct b.
      * (* b = nil *)
        admit.
      * (* b = cons _ _ *)
        discriminate H.
    + (* ff = impure _ _; fb = impure _ _ *)
      discriminate H.
  - (* fq = impure _ _ *)
    discriminate H.
Abort.

Theorem prop_inv_add : forall (Shape : Type)
  (Pos : Shape -> Type)
  {a : Type} (total_a : Free Shape Pos a -> Prop)
  (x : Free Shape Pos a)
  (q : Free Shape Pos (QueueI Shape Pos a)),
  total_queue Shape Pos total_a q ->
  (invariant Shape Pos q = True_ Shape Pos) ->
  (invariant Shape Pos (addI Shape Pos x q) = True_ Shape Pos).
Proof.
  intros Shape Pos a total_a fx fq Htotal H.
  destruct Htotal as [ff fb HtotalF HtotalB]. (* fq = Pair_ ff fb *)
  destruct HtotalF; reflexivity.
Qed.
