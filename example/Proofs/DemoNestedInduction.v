From Base Require Import Free Handlers.
From Base Require Import Prelude.
From Base Require Import Test.QuickCheck.

From Generated Require Import DemoNestedInduction.

Require Import Coq.Program.Equality.

Require Import FunctionalExtensionality.

Arguments ForFree _ _ {_}.
Arguments ForPair _ _ {_} {_}.
Arguments flipTree {_} {_} {_} {_} {_} {_}.

(* Property, that the [Pair]s in the [branch] constructor are always pure for a given [Tree]. *)
Inductive PurePairs {Shape : Type} {Pos : Shape -> Type} {A : Type} : Tree Shape Pos A -> Prop :=
| PurePairs_leaf   : forall (fx : Free Shape Pos A),
    PurePairs (leaf fx)
| PurePairs_branch : forall (fT1 fT2 : Free Shape Pos (Tree Shape Pos A)),
    ForFree Shape Pos PurePairs fT1 -> ForFree Shape Pos PurePairs fT2 ->
    PurePairs (branch (Pair_ Shape Pos fT1 fT2)).

(* Lemma to handle an equation with a function taking two args. *)
Lemma f_equal2 :
  forall (A B C : Type)
         (f : A -> B -> C)
         (x1 x2 : A)
         (y1 y2 : B),
  x1 = x2 -> y1 = y2 -> f x1 y1 = f x2 y2.
Proof.
  intros A B C f x1 x2 y1 y2 EqX EqY;
  rewrite EqX;
  rewrite EqY;
  reflexivity.
Qed.

(* Simplification lemma for [flipTree]. *)
Lemma def_flipTree_branch :
  forall (Shape : Type) (Pos : Shape -> Type)
         `{Injectable Share.Shape Share.Pos Shape Pos}
         (a : Type)
         `{ShareableArgs Shape Pos a}
         (ft1 ft2 : Free Shape Pos (Tree Shape Pos a)),
  flipTree (Branch Shape Pos (Pair_ Shape Pos ft1 ft2)) =
  Branch Shape Pos (Pair_ Shape Pos (flipTree ft2) (flipTree ft1)).
Proof. trivial. Qed.

(* [flipTree] is involutive, if the [Pair]s in the given tree do not contain any effects. *)
Lemma flipTree_involutive :
   forall (Shape : Type)
          (Pos : Shape -> Type)
          `{Injectable Share.Shape Share.Pos Shape Pos}
          (A : Type)
          `{ShareableArgs Shape Pos A}
          `{Normalform Shape Pos A}
          (fTree : Free Shape Pos (Tree Shape Pos A)),
  ForFree Shape Pos PurePairs fTree ->
  quickCheck (prop_flipTree_involutive Shape Pos Cbneed fTree).
Proof.
  intros Shape Pos Inj A ShrArgs Nf fTree HPure.
  simpl.
  induction fTree as [tree | sTree pfTree IHpfTree].
  - dependent destruction HPure; rename H into HPure.
    induction tree as [fValue | fPair IHfPair] using Tree_Ind.
    + (* fTree = Leaf fValue *)
      (* Trivial case. *)
      simpl flipTree.
      reflexivity.
    + (* fTree = Branch fPair *)
      destruct fPair as [pair | sPair pfPair].
      * simplify IHfPair as IH.
        destruct pair as [fT1 fT2].
        inversion IH as [fx fy IHt1 IHt2] ; clear IH; subst.
        dependent destruction HPure; rename H into HPure1; rename H0 into HPure2.
        (* fTree = Branch (Pair_ fT1 fT2) *)
        rewrite def_flipTree_branch.
        rewrite def_flipTree_branch.
        apply f_equal2 with
          (f := fun x y => Branch _ _ (Pair_ _ _ x y)).
        -- clear HPure2 IHt2 fT2.
           induction fT1 as [t1 | sT1 pfT1 IHpfT1].
           ++ (* Apply induction hypothesis gained from the induction over [fTree]. *)
              simplify IHt1 as IH.
              dependent destruction HPure1; rename H into HPure1.
              apply (IH HPure1).
           ++ (* Apply induction hypothesis gained from the induction over [fT1]
                 combined with
                 the induction hypothesis gained from the induction over [fTree]. *)
              simpl.
              apply f_equal.
              extensionality p.
              dependent destruction IHt1; rename H into IHt1.
              dependent destruction HPure1; rename H into HPure1.
              apply (IHpfT1 p (HPure1 p) (IHt1 p)).
        -- clear HPure1 IHt1 fT1.
           induction fT2 as [t2 | sT2 pfT2 IHpfT2].
           ++ (* Apply induction hypothesis gained from the induction over [fTree]. *)
              simplify IHt2 as IH.
              dependent destruction HPure2; rename H into HPure2.
              apply (IH HPure2).
           ++ (* Apply induction hypothesis gained from the induction over [fT1]
                 combined with
                 the induction hypothesis gained from the induction over [fTree]. *)
              simpl.
              apply f_equal.
              extensionality p.
              dependent destruction IHt2; rename H into IHt2.
              dependent destruction HPure2; rename H into HPure2.
              apply (IHpfT2 p (HPure2 p) (IHt2 p)).
      * (* fTree = Branch (impure sPair pfPair) *)
        (* This is a violation to [HPure].*)
        dependent destruction HPure.
  - (* fTree = impure sTree pfTree *)
    (* A induction hypothesis gained form the induction over [fTree]. *)
    dependent destruction HPure; rename H into HPure.
    simpl.
    f_equal.
    extensionality p.
    apply (IHpfTree p (HPure p)).
Qed.

Notation MShape := (Comb.Comb.Shape Maybe.Maybe.Shape Share.Share.Shape).
Notation MPos   := (Comb.Comb.Pos   Maybe.Maybe.Pos   Share.Share.Pos  ).
Import Maybe.Maybe.Monad.
Arguments Nothing {_} {_} {_} {_}.

(* Simplification lemma for the [Maybe] monad. *)
Lemma impureUndefined :
  forall (A  : Type)
         (s  : Maybe.Maybe.Shape)
         (pf : Maybe.Maybe.Pos s -> Free MShape MPos A),
  impure (inl s) pf = undefined.
Proof.
  intros A s pf; destruct s; simpl;
  unfold Nothing; simpl;
  f_equal; extensionality p; destruct p.
Qed.

(* The lemma show above does not hold, if there is a [Pair] the [Tree] that is impure. *)
Example flipTree_involutive_counterexample :
  not (quickCheck (prop_flipTree_involutive MShape MPos Cbneed (Branch MShape MPos undefined))).
Proof.
  simpl; rewrite allUndefined; simpl.
  intro H; discriminate H.
Qed.
