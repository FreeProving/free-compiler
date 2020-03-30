From Base Require Import Free Prelude Test.QuickCheck.
From Generated Require Import ListFunctor.

Require Import Coq.Logic.FunctionalExtensionality.

Theorem prop_map_id : forall (Shape : Type) (Pos : Shape -> Type) {t0 : Type},
  @eqProp Shape Pos (Free Shape Pos (List Shape Pos t0) -> Free Shape Pos (List Shape Pos t0)) 
  (pure (fun x_0 => @map Shape Pos t0 t0 (pure (fun x_1 => @id Shape Pos t0 x_1)) x_0)) 
  (pure (fun x_0 => @id Shape Pos (List Shape Pos t0) x_0)).
Proof.
  intros Shape Pos t0. unfold eqProp. unfold id.
  apply f_equal. extensionality fxs.
  induction fxs using FreeList_ind 
    with (P := fun xs => map_1 Shape Pos t0 t0 (pure (fun x_1 : Free Shape Pos t0 => x_1)) xs = pure xs).
  - (* fxs = pure nil *)              simpl. reflexivity.
  - (* fxs = pure (cons fxs1 fxs2) *) simpl. unfold Cons. do 2 apply f_equal. apply IHfxs1.
  - (* fxs = pure xs *)               simpl. apply IHfxs.
  - (* fxs = impure s pf *)           simpl. apply f_equal. extensionality p. apply H.
Qed.