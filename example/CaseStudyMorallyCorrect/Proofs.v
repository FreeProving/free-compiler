From Base Require Import Test.QuickCheck.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.
From Base Require Import Prelude.List.
From Generated Require Import FastLooseBasic.
From Proofs Require Import AppendProofs.
From Proofs Require Import Simplify.
From Proofs Require Import PeanoInd.
From Proofs Require Import SimplLemmas.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Arguments rev {_} {_} {_} _ _.
Arguments rev_0 {_} {_} {_} _ _.
Arguments reverse {_} {_} {_} _ .
Arguments reverseNaive {_} {_} {_} _ .
Arguments reverseNaive_0 {_} {_} {_} _ .
Arguments append {_} {_} {_} _ _.
Arguments Nil {_} {_} {_}.
Arguments Cons {_} {_} {_} _ _.
Arguments plus {_} {_} _ _.
Arguments minus {_} {_} _ _.
Arguments pred {_} {_} _.
Arguments map {_} {_} {_} {_} _ _.
Arguments comp {_} {_} {_} {_} {_} _ _.
Arguments id {_} {_} {_} _.
Arguments S {_} {_} _.
Arguments Zero {_} {_}.

Section reverseIsReverseNaive.

Lemma rev_acc_and_rest_list_connection': forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (xs : List Shape Pos A) (facc : Free Shape Pos (List Shape Pos A)),  
  rev (pure xs) facc = append (reverse (pure xs)) facc.
Proof.
  intros Shape Pos A xs.
  induction xs as [ | fx fxs' IHfxs'] using List_Ind; intros facc.
  - reflexivity.
  - induction fxs' as [ xs' | sh pos IHpos] using Free_Ind; rewrite cons_Cons; unfold reverse; do 2 rewrite apply_rev. 
    + simplify2 IHfxs' as IH. rewrite IH.
      rewrite IH with (facc := Cons fx Nil).
      rewrite <- append_assoc. reflexivity.
    + simpl. f_equal. extensionality x. simplify2 IHpos as IH. apply IH.
Qed.

Lemma rev_acc_and_rest_list_connection: forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fxs : Free Shape Pos (List Shape Pos A)) (facc : Free Shape Pos (List Shape Pos A)),
  rev fxs facc = append (reverse fxs) facc.
Proof.
  intros Shape Pos A fxs facc.
  induction fxs as [ xs | sh pos IHpos ] using Free_Ind.
  - apply rev_acc_and_rest_list_connection'.
  - simpl. f_equal. extensionality x. apply IHpos.
Qed.

Lemma reverse_is_reverseNaive': forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (xs : List Shape Pos A),
  reverse (pure xs) = reverseNaive (pure xs).
Proof.
  intros Shape Pos A xs.
  induction xs as [ | fx fxs' IHfxs' ] using List_Ind.
  - reflexivity.
  - induction fxs' as [ xs' | sh pos IHpos ] using Free_Ind; rewrite cons_Cons; unfold reverse; rewrite apply_reverseNaive; rewrite apply_rev.
    + simplify IHfxs' as IH.
      rewrite rev_acc_and_rest_list_connection. rewrite IH. reflexivity.
    + simpl. f_equal. extensionality x. simplify2 IHpos as IH. apply IH.
Qed.

Theorem reverse_is_reverseNaive: quickCheck prop_reverse_is_reverseNaive.
Proof.
  simpl.
  intros Shape Pos A fxs.
  induction fxs as [ xs | sh pos IHpos ] using Free_Ind.
  - apply reverse_is_reverseNaive'.
  - simpl. f_equal. extensionality x. apply IHpos.
Qed.

End reverseIsReverseNaive.


Section reverse_is_involution.

Lemma reverseNaive_append : forall (A : Type)
  (fxs fys : Free Identity.Shape Identity.Pos (List Identity.Shape Identity.Pos A)),
      reverseNaive (append fxs fys) = append (reverseNaive fys) (reverseNaive fxs).
Proof.
intros A fxs.
destruct fxs as [ xs | [] _ ].
- induction xs as [| fx fxs' IHfxs'] using List_Ind; intros.
  + rewrite append_nil. simpl. reflexivity.
  + destruct fxs' as [ xs' | [] pf].
    * rewrite cons_Cons. rewrite apply_reverseNaive. 
      rewrite append_assoc.
      simplify2 IHfxs' as IHxs'.
      rewrite <- IHxs'. reflexivity.
Qed.

Theorem reverseNaive_is_involution: forall (A : Type)
 (fxs : Free Identity.Shape Identity.Pos (List Identity.Shape Identity.Pos A)),
  reverseNaive (reverseNaive fxs) = fxs.
Proof.
  intros A fxs.
  destruct fxs as [ xs | [] _ ].
  - induction xs as [ | fx fxs' IHfxs' ] using List_Ind.
    + reflexivity.
    + destruct fxs' as [ xs' | [] pf].
      * rewrite cons_Cons. rewrite apply_reverseNaive. rewrite reverseNaive_append. 
        simplify2 IHfxs' as IHxs'. rewrite IHxs'. reflexivity.
Qed.

Theorem reverse_is_involution: quickCheck (@prop_rev_is_rev_inv Identity.Shape Identity.Pos).
Proof.
  simpl.
  intros A fxs.
  do 2 rewrite reverse_is_reverseNaive. 
  apply reverseNaive_is_involution.
Qed.

End reverse_is_involution.

Section minus_is_plus_inverse.

Lemma plus_zero': forall (Shape : Type) (Pos : Shape -> Type)
  (x : Peano Shape Pos),
  plus Zero (pure x) = (pure x).
Proof.
  intros Shape Pos x.
  induction x as [ | fx' IHfx' ] using Peano_Ind.
  - reflexivity.
  - induction fx' as [ x' | sh pos IHpos ] using Free_Ind; rewrite s_S; unfold plus; rewrite apply_foldPeano; f_equal.
    + simplify2 IHfx' as IH. apply IH.
    + simpl. f_equal. extensionality x. simplify2 IHpos as IH.
      apply IH.
Qed.

Lemma plus_zero: forall (Shape : Type) (Pos : Shape -> Type)
  (fx : Free Shape Pos (Peano Shape Pos)),
  plus Zero fx = fx.
Proof.
  intros Shape Pos fx.
  induction fx as [ x | pf sh IHpos ] using Free_Ind.
  - apply plus_zero'.
  - simpl. f_equal. extensionality x. apply IHpos.
Qed.

Lemma plus_s : forall (fx fy : Free Identity.Shape Identity.Pos (Peano Identity.Shape Identity.Pos)),
  plus (S fy) fx = S (plus fy fx).
Proof.
  intros fx fy.
  destruct fx as [ x | [] _ ].
  induction x as [ | fx' IHfx' ] using Peano_Ind.
  - reflexivity.
  - destruct fx' as [ x' | [] _ ]; rewrite s_S.
    + simplify2 IHfx' as IH. unfold plus. rewrite apply_foldPeano. f_equal.
      simpl. apply IH. 
Qed.

Lemma minus_pred : forall (Shape : Type) (Pos : Shape -> Type)
  (fy fx: Free Shape Pos (Peano Shape Pos)) ,
  minus fx (S fy) = minus (pred fx) fy.
Proof.
  intros Shape Pos fy fx.
  induction fy as [ y | sh pos IHpos ] using Free_Ind.
  - induction y as [ | fy' IHfy' ] using Peano_Ind. 
    + reflexivity.
    + induction fy' as [ y' | sh pos IHpos ] using Free_Ind; 
      rewrite s_S; unfold minus; rewrite apply_foldPeano; simpl; f_equal.
      * simplify2 IHfy' as IH. apply IH.
      * extensionality x. simplify2 IHpos as IH. apply IH.
  - simpl. f_equal. extensionality x. apply IHpos.
Qed.

Lemma pred_succ: forall (Shape : Type) (Pos : Shape -> Type)
  (fx: Free Shape Pos (Peano Shape Pos)),
   pred (S fx) = fx.
Proof.
  intros Shape Pos fx.
  destruct fx as [ x | sh pf ].
  - destruct x as [ | fx' ].
    + reflexivity.
    + destruct fx' as [ x' | sh pf ]; reflexivity.
  - reflexivity.
Qed.

Theorem minus_is_plus_inv_ext: quickCheck (@prop_minus_plus_inv Identity.Shape Identity.Pos).
Proof.
  simpl quickCheck.
  intros fx fy.
  destruct fy as [ y | [] _ ].
  induction y as [ | fy' IHfy' ] using Peano_Ind. 
  - simpl. apply plus_zero.
  - destruct fy' as [ y' | [] _ ].
    + rewrite s_S. simplify2 IHfy' as IH. rewrite plus_s. rewrite minus_pred. rewrite pred_succ. apply IH.
Qed.

Lemma minus_plus_inv: forall (fy : Free Identity.Shape Identity.Pos (Peano Identity.Shape Identity.Pos)),
  comp (pure (fun fx => minus fx fy)) (pure (fun fx => plus fy fx)) = id.
Proof.
  intros fy.
  extensionality fx.
  simpl.
  apply minus_is_plus_inv_ext.
Qed.


End minus_is_plus_inverse.

Section small_helping_lemmas.

Lemma comp_id : forall (Shape : Type) (Pos : Shape -> Type) (A B : Type)
 (f :(Free Shape Pos A -> Free Shape Pos B)),
  (pure (comp (pure id) (pure f))) = @pure Shape Pos (Free Shape Pos A -> Free Shape Pos B) f.
Proof.
  intros Shape Pos A B ff.
  f_equal.
Qed.


Lemma map_fusion : forall (Shape : Type) (Pos : Shape -> Type) (A B C : Type) 
  (ff : Free Shape Pos (Free Shape Pos B -> Free Shape Pos C))
  (fg : Free Shape Pos (Free Shape Pos A -> Free Shape Pos B)),
  comp (pure (map ff)) (pure (map fg)) = map (pure (comp ff fg)).
Proof.
  intros Shape Pos A B C ff gg.
  extensionality fxs.
  induction fxs as [ xs | sh pos IHpos ] using Free_Ind.
  - induction xs as [| fx fxs' IHfxs ] using List_Ind.
    + reflexivity.
    + induction fxs' as [ xs' | sh pos IHpos ] using Free_Ind; rewrite cons_Cons.
      * simpl. f_equal.
        simplify2 IHfxs as IH. apply IH.
      * simpl. do 2 f_equal. extensionality x. simplify2 IHpos as IH. apply IH.
  - simpl. f_equal. extensionality x. apply IHpos.
Qed.

Lemma map_id_ext : quickCheck prop_map_id.
Proof.
  simpl.
  intros Shape Pos A fxs.
  unfold id.
  induction fxs as [ xs | sh pos IHpos ] using Free_Ind.
  - induction xs as [| fx fxs' IHfxs ] using List_Ind.
    + reflexivity.
    + induction fxs' as [ xs' | sh pos IHpos ] using Free_Ind;
      rewrite cons_Cons; rewrite apply_map; f_equal. 
      * simplify2 IHfxs as IH. apply IH.
      * simpl. f_equal. extensionality x. simplify2 IHpos as IH. apply IH.
  - simpl. f_equal. extensionality x. apply IHpos.
Qed.

Lemma map_id : forall (Shape : Type) (Pos : Shape -> Type) (A : Type),
  @map Shape Pos A A (pure id) = id.
Proof.
  intros Shape Pos A.
  extensionality fxs.
  apply map_id_ext.
Qed.

Lemma compose_assoc : forall (Shape : Type) (Pos : Shape -> Type) (A B C D : Type) 
  (fcd : Free Shape Pos (Free Shape Pos C -> Free Shape Pos D))
  (fbc : Free Shape Pos (Free Shape Pos B -> Free Shape Pos C))
  (fab : Free Shape Pos (Free Shape Pos A -> Free Shape Pos B)),
  (comp (pure (comp fcd fbc)) fab)  = (comp fcd (pure (comp fbc fab))).
Proof.
  intros Shape Pos A B C D fcd fbc fab.
  destruct fcd as [ cd | sh pos ]; reflexivity.
Qed.

End small_helping_lemmas.

Section main_proof.

Opaque comp.

Theorem fancy_id : quickCheck (@prop_morally_correct Identity.Shape Identity.Pos).
Proof.
  simpl quickCheck.
  intros fy fxs.
  rewrite compose_assoc.
  rewrite <- compose_assoc with (fcd := pure (map (pure (fun x => minus x fy)))).
  rewrite map_fusion.  
  rewrite minus_plus_inv.
  rewrite map_id.
  rewrite comp_id.
Transparent comp.
  simpl. 
  apply reverse_is_involution.
Qed.

End main_proof.