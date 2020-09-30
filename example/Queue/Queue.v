(* This example contains the code for the case study from the bachelor's
   thesis https://freeproving.github.io/free-compiler/thesis/Andresen2019.pdf
   In the thesis we've looked at the definition of queues that does not use
   pattern matching on the left-hand sides of function declarations.
   Since then experimental support for pattern matching compilation has
   been added to the compiler.
   Replace the imports of `Queue.WithoutPatternMatching` by
   `Queue.WithPatternMatching` to try out the version that uses pattern
   matching compilation.
*)

From Base Require Import Free Prelude Test.QuickCheck.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

From Generated Require Import Queue.WithoutPatternMatching.Lemmas.
From Generated Require Import Queue.WithoutPatternMatching.Props.
From Generated Require Import Queue.WithoutPatternMatching.Queue.
From Generated Require Import Queue.WithoutPatternMatching.QueueI.
From Generated Require Import Queue.WithoutPatternMatching.Util.

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

Lemma is_pure_true_or : quickCheck prop_is_pure_true_or.
Proof.
  intros Shape Pos fb1 fb2 Hpure.
  destruct fb1 as [ b1 |], fb2 as [ b2 |]; simpl in *.
  - (* fb1 = pure b1,    fb2 = pure b2 *)    destruct b1; auto.
  - (* fb1 = pure b1,    fb2 = impure _ _ *) destruct b1; auto.
  - (* fb1 = impure _ _, fb2 = pure b2 *)    contradiction Hpure.
  - (* fb1 = impure _ _, fb2 = impure _ _ *) contradiction Hpure.
Qed.

Lemma is_pure_true_and : quickCheck prop_is_pure_true_and.
Proof.
  intros Shape Pos fb1 fb2 Hpure.
  destruct fb1 as [ b1 |], fb2 as [ b2 |] ; simpl in *.
  - (* fb1 = pure b1,    fb2 = pure b2 *)    destruct b1, b2; auto.
  - (* fb1 = pure b1,    fb2 = impure _ _ *) destruct b1; auto. discriminate Hpure.
  - (* fb1 = impure _ _, fb2 = pure b2 *)    contradiction Hpure.
  - (* fb1 = impure _ _, fb2 = impure _ _ *) contradiction Hpure.
Qed.

Lemma null_rev : quickCheck prop_null_rev.
Proof.
  intros Shape Pos a fxs Hnull.
  destruct fxs as [ xs |  ].
  - (* fxs = pure xs *)
    destruct xs.
    + (* xs = nil *) trivial.
    + (* xs = cons _ _ *) discriminate Hnull.
  - (* fxs = impure _ _ *)
    contradiction Hnull.
Qed.

Lemma append_nil : quickCheck prop_append_nil.
Proof.
  intros Shape Pos a NF fxs.
  induction fxs using FreeList_ind with (P := fun xs => append1 Shape Pos a (pure nil) xs = pure xs); simpl.
  - reflexivity.
  - simpl; repeat apply f_equal. apply IHfxs1.
  - apply IHfxs.
  - repeat apply f_equal. extensionality p. apply H.
Qed.

Lemma append1_assoc :
  forall (Shape : Type)
         (Pos : Shape -> Type)
         {a : Type}
         (xs : List Shape Pos a)
         (fys fzs : Free Shape Pos (List Shape Pos a)),
      append1 Shape Pos a (append Shape Pos fys fzs) xs
      = append Shape Pos (append1 Shape Pos a fys xs) fzs.
Proof.
  intros Shape Pos a xs fys fzs.
  induction xs using List_Ind.
  - reflexivity.
  - induction fxs using Free_Ind.
    + simpl. simplify H as IH. rewrite IH. reflexivity.
    + (*Inductive case: [fxs = impure s pf] with induction hypothesis [H] *)
      simpl. do 3 apply f_equal. extensionality p.
      simplify H as IH. apply IH.
Qed.

Lemma append_assoc : quickCheck prop_append_assoc.
Proof.
  intros Shape Pos a NF fxs fys fzs.
  induction fxs as [ | s pf IH ] using Free_Ind.
  - simpl. apply append1_assoc.
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
Theorem prop_isEmpty_theorem : forall (Shape : Type)
  (Pos : Shape -> Type)
  {a : Type} `{NF : Normalform Shape Pos a} (total_a : Free Shape Pos a -> Prop)
  (qi : Free Shape Pos (QueueI Shape Pos a)),
  total_queue Shape Pos total_a qi -> quickCheck (@prop_isEmpty Shape Pos a NF qi).
Proof.
  intros Shape Pos a total_a NF fqi Htotal Hinv.
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
           symmetry. unfold isEmpty. apply pure_bool_toProperty in Hnull. apply Hnull.
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
Theorem prop_isEmpty_theorem' : quickCheck prop_isEmpty.
Proof.
  intros Shape Pos a NF fqi Hinv.
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
           symmetry. unfold isEmpty. apply pure_bool_toProperty in Hnull. apply Hnull.
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
            specialize (append_nil Shape Pos a NF) as appNil. 
            simpl in appNil. unfold isEmpty. rewrite appNil. reflexivity.
         ++ (* reverse Shape Pos fys = Cons Shape Pos y ys' *)
            simpl in Hnull. discriminate Hnull.
         ++ (* reverse Shape Pos fys = impure _ _*)
            simpl in Hnull. contradiction Hnull.
      -- (* impure _ _ = True_ Shape Pos *)
         contradiction Hcontra.
  - (* fqi = impure _ _ *)
    simpl in Hinv. contradiction Hinv.
Qed.

(* In order to prove [prop_add] no totality constraint is necessary. *)
Theorem prop_add_theorem : quickCheck prop_add.
Proof.
  intros Shape Pos a NF fx fqi.
  induction fqi as [ [f1 f2] | eq ] using Free_Ind; simpl.
  - destruct f1 as [l | s pf]; simpl.
    + destruct l as [ | fy fys]; simpl.
      * specialize (append_nil Shape Pos a NF) as appNil. simpl in appNil.
        rewrite appNil. reflexivity.
      * apply (append_assoc Shape Pos _ NF (pure (cons fy fys)) (reverse Shape Pos f2) (singleton Shape Pos fx)).
    + repeat apply f_equal. extensionality p.
      induction (pf p) as [fys |] using Free_Ind; simpl.
      * destruct fys; simpl.
        -- specialize (append_nil Shape Pos a NF) as appNil. simpl in appNil. rewrite appNil.
           reflexivity.
        -- do 2 apply f_equal. apply (append_assoc Shape Pos _ NF f0 (reverse Shape Pos f2) (singleton Shape Pos fx)).
      * repeat apply f_equal.
        extensionality p1.
        apply H.
  - repeat apply f_equal.
    extensionality p.
    apply H.
Qed.

(* We have to add a totality constraint to [prop_front]. *)
Theorem prop_front_theorem : forall Shape Pos P a NF total_a qi,
  total_queue Shape Pos total_a qi -> quickCheck (@prop_front Shape Pos P a NF qi).
Proof.
  intros Shape Pos P a total_a NF fqi Htotal HinvNempty.
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

(* Since the compiler is now adding vanishing type arguments automatically,
   the [prop_inv_empty] can be proven without a problem. *)
Theorem prop_inv_empty_theorem : quickCheck prop_inv_empty.
Proof.
  intros Shape Pos t0. simpl. reflexivity.
Qed.

(* Proving [prop_inv_add] requires a totality constraint.
   Otherwise we get stuck in the case admitted below. *)
Theorem prop_inv_add_theorem : quickCheck prop_inv_add.
Proof.
  intros Shape Pos a fx fq H. destruct fq as [[ff fb] |].
  - (* fq = Pair_ Shape Pos ff fb *)
    destruct ff as [f |]; destruct fb as [b |].
    + (* ff = pure f; fb = pure b *)
      destruct f; reflexivity.
    + (* ff = pure f; fb = impure _ _ *)
      contradiction H.
    + (* ff = impure _ _; fb = pure b *)
      destruct b.
      * (* b = nil *)
        admit.
      * (* b = cons _ _ *)
        contradiction H.
    + (* ff = impure _ _; fb = impure _ _ *)
      contradiction H.
  - (* fq = impure _ _ *)
    contradiction H.
Abort.

(* To add the totality constraint we have to introduce all arguments of [prop_inv_add]
   first. However, we do not have to repeat the type annotations here. *)
Theorem prop_inv_add_theorem : forall Shape Pos a total_a x q,
  total_queue Shape Pos total_a q -> quickCheck (@prop_inv_add Shape Pos a x q).
Proof.
  intros Shape Pos a total_a fx fq Htotal H.
  destruct Htotal as [ff fb HtotalF HtotalB]. (* fq = Pair_ ff fb *)
  destruct HtotalF; reflexivity.
Qed.
