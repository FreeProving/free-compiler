From Base Require Import Free.
From Base Require Import Prelude.List.
From Generated Require Import FastLooseBasic.

Arguments Nil {_} {_} {_}.
Arguments Cons {_} {_} {_} _ _.
Arguments S {_} {_} _.
Arguments Zero {_} {_}.
Arguments append {_} {_} {_} _ _.
Arguments rev {_} {_} {_} _ _.
Arguments reverse {_} {_} {_} _ .
Arguments reverseNaive {_} {_} {_} _ .
Arguments plus {_} {_} _ _.
Arguments minus {_} {_} _ _.
Arguments pred {_} {_} _.
Arguments map {_} {_} {_} {_} _ _.
Arguments foldPeano {_} {_} {_} _ _ _.

Lemma cons_Cons: forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fx : Free Shape Pos A) ( fxs : Free Shape Pos (List Shape Pos A)),
  pure (cons fx fxs) = Cons fx fxs.
Proof.
  reflexivity.
Qed.

Lemma nil_Nil: forall (Shape : Type) (Pos : Shape -> Type) (A : Type),
  pure (@nil Shape Pos A) = Nil.
Proof.
  reflexivity.
Qed.

Lemma apply_append_nil: forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fxs : Free Shape Pos (List Shape Pos A)),
  append Nil fxs = fxs.
Proof.
  reflexivity.
Qed.

Lemma apply_append_cons: forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fx : Free Shape Pos A) ( fxs fys : Free Shape Pos (List Shape Pos A)),
  append (Cons fx fxs) fys = Cons fx (append fxs fys).
Proof.
  reflexivity.
Qed.

Lemma apply_reverseNaive: forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fx : Free Shape Pos A) (fxs : Free Shape Pos (List Shape Pos A)),
  reverseNaive (Cons fx fxs) =  append (reverseNaive fxs) (Cons fx Nil).
Proof.
  reflexivity.
Qed.

Lemma apply_rev: forall (Shape : Type) (Pos : Shape -> Type) (A : Type)
  (fx : Free Shape Pos A) (fxs fys: Free Shape Pos (List Shape Pos A)),
  rev (Cons fx fxs) fys = rev fxs (Cons fx fys).
Proof.
  reflexivity.
Qed.

Lemma apply_map: forall (Shape : Type) (Pos : Shape -> Type) (A B : Type)
  (fx : Free Shape Pos A) (fxs : Free Shape Pos (List Shape Pos A)) 
  (ff : Free Shape Pos (Free Shape Pos A -> Free Shape Pos B)),
  map ff (Cons fx fxs) = Cons (ff >>= (fun f => f fx)) (map ff fxs).
Proof.
  reflexivity.
Qed.

Lemma s_S: forall (Shape : Type) (Pos : Shape -> Type) (fn : Free Shape Pos (Peano Shape Pos)),
  pure (s fn) = S fn.
Proof.
  reflexivity.
Qed.

Lemma zero_Zero: forall (Shape : Type) (Pos : Shape -> Type),
  pure (@zero Shape Pos) = Zero.
Proof.
  reflexivity.
Qed.

Lemma apply_pred: forall (Shape : Type) (Pos : Shape -> Type) (fn : Free Shape Pos (Peano Shape Pos)),
  pred (S fn) = fn. 
Proof.
  reflexivity.
Qed.

Lemma apply_foldPeano: forall (Shape : Type) (Pos : Shape -> Type) (A : Type) 
  (f : Free Shape Pos A -> Free Shape Pos A) (fa : Free Shape Pos A) (fn : Free Shape Pos (Peano Shape Pos)),
  foldPeano (pure f) fa (S fn) = f (foldPeano (pure f) fa fn).
Proof.
  reflexivity.
Qed.



