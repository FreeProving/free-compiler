(* This file is a variant of [RazorProofsPureCodes] but it is using the advanced
   tactics of [Extra/FreeDB]. *)

From Base Require Import Free Free.Instance.Maybe Free.Instance.Error Prelude Test.QuickCheck.
From Generated Require Import Razor.
From Razor.Extra Require Import FreeDB Tactic Pureness.
From Proofs Require Import AppendAssocProofs.
Import AppendAssoc.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

(* This property states that the given Partial instance represents every [undefined] as an impure value. *)
Definition UndefinedIsImpure {Shape : Type} {Pos : Shape -> Type} (Part : Partial Shape Pos): Prop :=
  forall (A : Type),
  exists (s : Shape) (pf : (Pos s) -> Free Shape Pos A),
      undefined = impure s pf.

(* The property holds for the [Maybe] monad and the [Error] monad. *)
Example undefinedIsImpureMaybe : UndefinedIsImpure (Maybe.Partial Maybe.Shape Maybe.Pos).
Proof.
  intro A.
  simpl. unfold Nothing. exists tt.
  exists (fun p : Maybe.Pos tt => match p return (Free unit Maybe.Pos A) with end).
  reflexivity.
Qed.

Example undefinedIsImpureError : UndefinedIsImpure (Error.Partial (Error.Shape string) Error.Pos).
Proof.
  intro A.
  simpl. unfold ThrowError. exists "undefined"%string.
  exists (fun p : Error.Pos "undefined"%string => match p return (Free string Error.Pos A) with end).
  reflexivity.
Qed.

(* This property states that the given Partial instance has no positions in an impure [undefined]. *)
Definition UndefinedHasNoPositions {Shape : Type} {Pos : Shape -> Type} (Partial : Partial Shape Pos): Prop :=
  forall (A : Type)
         (s : Shape)
         (pf : (Pos s) -> Free Shape Pos A),
  undefined = impure s pf ->
  forall (p : Pos s),
      False.

Section Proofs_PureCodes.

  Variable Shape : Type.
  Variable Pos   : Shape -> Type.
  Context `{Injectable Share.Shape Share.Pos Shape Pos}.
  Variable Part  : Partial Shape Pos.

  (* If the code is pure and the first operation is pure if there is any, an
     [exec] call on an undefined stack will result in an undefined stack. *)
  Lemma exec_strict_on_stack_arg_Nil :
    UndefinedIsImpure Part ->
    UndefinedHasNoPositions Part ->
        exec_ Part Nil_ undefined
        = undefined.
  Proof.
    intros HUndefined1 HUndefined2.
    specialize (HUndefined1 (Stack Shape Pos)).
    destruct HUndefined1 as [ s [ pf HUndefined1 ] ].
    rewrite HUndefined1.
    autodef.
    f_equal.
    extensionality p.
    specialize (HUndefined2 (Stack Shape Pos) s pf HUndefined1 p).
    destruct HUndefined2.
  Qed.

  Lemma exec_strict_on_stack_arg_Op :
    UndefinedIsImpure Part ->
    UndefinedHasNoPositions Part ->
    forall (op : Op Shape Pos)
           (fcode : Free Shape Pos (Code Shape Pos)),
        exec_ Part (Cons_ (pure op) fcode) undefined
        = undefined.
  Proof.
    intros HUndefined1 HUndefined2 op fcode.
    specialize (HUndefined1 (Stack Shape Pos)).
    destruct HUndefined1 as [ s [ pf HUndefined1 ] ].
    rewrite HUndefined1.
    autodef.
    f_equal.
    extensionality p.
    specialize (HUndefined2 (Stack Shape Pos) s pf HUndefined1 p).
    destruct HUndefined2.
  Qed.

  (* If [UndefinedIsImpure] and [UndefinedHasNoPositions] hold and we are given
     two recursively pure pieces of code and a stack, we know that it doesn't
     matter whether we concatenate those pieces of code and run them on the
     stack, or run the first piece of code on the stack and run the second
     piece of code on the resulting stack afterwards. *)
  Lemma exec_append :
    UndefinedIsImpure Part ->
    UndefinedHasNoPositions Part ->
    forall (fcode1 : Free Shape Pos (Code Shape Pos)),
    RecPureCode fcode1 ->
    forall (fcode2 : Free Shape Pos (Code Shape Pos)),
    RecPureCode fcode2 ->
    forall (fstack : Free Shape Pos (Stack Shape Pos)),
        exec_ Part (append_ fcode1 fcode2) fstack
        = exec_ Part fcode2 (exec_ Part fcode1 fstack).
  Proof with pretty; unfold Code; unfold Stack; try reflexivity.
    intros HUndefined1 HUndefined2 fcode1 HPure1 fcode2 HPure2.
    (* As we now that both pieces of code are recursively pure, we can
       immediately destruct the monadic layer.*)
    destruct fcode1 as [ code1 | ]; try eliminate_pureness_property_impure.
    destruct fcode2 as [ code2 | ]; try eliminate_pureness_property_impure.
    induction code1 as [ | [ [ fn | ] | ] fcode1' IHfcode1' ] using List_ind;
      try eliminate_pureness_property_impure...
    - (* code1 = [] *)
      (* This case is trivial. *)
      intro fstack.
      autodef.
      f_equal.
      induction fstack as [ stack | sStack pfStack IHpfStack ]; autodef; autoIH.
    - (* code1 = (PUSH fn : fcode1') *)
      (* This case is also easy. *)
      intro fstack.
      destruct fcode1' as [ code1' | ]; try eliminate_pureness_property_impure.
      simplify IHfcode1' as IH.
      (* We can prove the goal per induction over the stack. *)
      induction fstack as [ stack | sStack pfStack IHpfStack ]; autodef;
        try (apply IH; prove_pureness_property).
      (* In the impure case we need to destruct the second piece of code to be able to simplify
         the goal before applying the induction hypothesis in the pure cases. *)
      destruct code2 as [ | [ op | ] fcode2' ]; autodef; try autoIH; eliminate_pureness_property_impure.
    - (* code1 = (ADD : fcode1') *)
      (* In this case the [exec] function might return [undefined] and we need
         our two assumptions for an [undefined] [Stack]. *)
      intro fstack.
      destruct fcode1' as [ code1' | ]; try eliminate_pureness_property_impure.
      simplify IHfcode1' as IH.
      (* As the addition reads two values from the stack, we need to destruct the stack. *)
      induction fstack as [ [ | fv1 fstack1 ] | sStack pfStack IHpfStack ]...
      + (* fstack = [] *)
        (* On both sides an [undefined] is returned. *)
        autodef.
        destruct code2 as [ | [ op | ] fcode2' ]; try eliminate_pureness_property_impure...
        -- symmetry; apply (exec_strict_on_stack_arg_Nil HUndefined1 HUndefined2)...
        -- rewrite (exec_strict_on_stack_arg_Op HUndefined1 HUndefined2)...
      + induction fstack1 as [ [ | fv2 fstack2 ] | sStack1 pfStack1 IHpfStack1 ]...
        * (* fstack = (fv1 : fstack1) *)
          (* On both sides an [undefined] is returned. *)
          autodef.
          destruct code2 as [ | [ op | ] fcode2' ]; try eliminate_pureness_property_impure...
          -- symmetry; apply (exec_strict_on_stack_arg_Nil HUndefined1 HUndefined2)...
          -- rewrite (exec_strict_on_stack_arg_Op HUndefined1 HUndefined2)...
        * (* fstack = (fv1 : fv2 : fstack2) *)
          (* The function definition can be applied and we can use the induction hypothesis. *)
          autodef.
          apply IH; prove_pureness_property.
        * (* fstack = (fv1 : impure sStack1 pfStack1) *)
          autodef.
          destruct code2 as [ | [ op | ] fcode2' ]; autodef; try autoIH; eliminate_pureness_property_impure.
      + (* fstack = impure sStack2 pfStack2 *)
        autodef.
        destruct code2 as [ | [ op | ] fcode2' ]; autodef; try autoIH; eliminate_pureness_property_impure.
  Qed.

End Proofs_PureCodes.