(* This file contains an alternative proof for one of the lemmas of the proof file
   [RazorProofs] under different preconditions. Notice that this proof contains
   complex impure cases that are not easy to solve with the default tactics and
   require to deal with lemmas on the [>>=] operator. *)
   
From Base Require Import Free Free.Instance.Maybe Free.Instance.Error Prelude Test.QuickCheck.
From Razor.Extra Require Import Tactic Pureness.
From Generated Require Import Razor.
From Proofs Require Import AppendAssocProofs.
Import AppendAssoc.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

(* This property states that the given Partial instance represents every [undefined] as an impure value. *)
Definition UndefinedIsImpure {Shape : Type} {Pos : Shape -> Type} (Partial : Partial Shape Pos): Prop :=
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

Example undefinedIsImpureError : UndefinedIsImpure (Error.Partial (Error.Shape string) (Error.Pos)).
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

  Variable Shape   : Type.
  Variable Pos     : Shape -> Type.
  Context `{Injectable Share.Shape Share.Pos Shape Pos}.
  Variable Partial : Partial Shape Pos.

  (* If the code is pure and the first operation is pure if there is any, the
     effect of an impure stack will transfer to the result of an exec call with
     that code and that stack. *)
  Lemma exec_strict_on_stack_arg_nil :
    forall (sStack  : Shape)
           (pfStack : Pos sStack -> Free Shape Pos (Stack Shape Pos)),
        exec Shape Pos Cbn Partial (Nil Shape Pos) (impure sStack pfStack)
        = impure sStack (fun p => exec Shape Pos Cbn Partial (Nil Shape Pos) (pfStack p)).
  Proof.
    intros sStack pfStack.
    reflexivity.
  Qed.

  Lemma exec_strict_on_stack_arg_cons :
    forall (op : Op Shape Pos)
           (fcode : Free Shape Pos (Code Shape Pos))
           (sStack  : Shape)
           (pfStack : Pos sStack -> Free Shape Pos (Stack Shape Pos)),
        exec Shape Pos Cbn Partial (Cons Shape Pos (pure op) fcode) (impure sStack pfStack)
        = impure sStack (fun p => exec Shape Pos Cbn Partial (Cons Shape Pos (pure op) fcode) (pfStack p)).
  Proof.
    intros op fcode sStack pfStack.
    destruct op as [ fn | ].
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma bind_pure :
    forall (A : Type)
           (fx : Free Shape Pos A),
        fx >>= pure = fx.
    Proof.
      inductFree fx as [ x | sX pfX IHpfX ]; reflexivity.
    Qed.

  Lemma bind_assoc :
    forall (A B C : Type)
           (fx : Free Shape Pos A) 
           (f : A -> Free Shape Pos B)
           (g : B -> Free Shape Pos C),
        (fx >>= f) >>= g
        = fx >>= fun fy => (f fy >>= g).
  Proof.
    intros A B C fx f g.
    inductFree fx as [ | sX pfX IHpfX ]; reflexivity.
  Qed.

  (* If there is a pattern matching on a [Stack] where both cases are handled
     the same way, we can skip the pattern matching. *)
  Lemma match_stack :
    forall (A : Type)
           (f : Stack Shape Pos -> Free Shape Pos A),
        (fun s => match s with
                  | nil => f nil
                  | cons fv fstack' => f (cons fv fstack')
                  end)
        = f.
  Proof.
    intros A f.
    extensionality s.
    destruct s as [ | fv fstack' ]; reflexivity.
  Qed.

  (* If [UndefinedIsImpure] and [UndefinedHasNoPositions] hold and we are given
     two recursively pure pieces of code and a stack, we know that it doesn't
     matter whether we concatenate those pieces of code and run them on the
     stack, or run the first piece of code on the stack and run the second
     piece of code on the resulting stack afterwards. *)
  Lemma exec_append :
    UndefinedIsImpure Partial ->
    UndefinedHasNoPositions Partial ->
    forall (fcode1 : Free Shape Pos (Code Shape Pos)),
    RecPureCode fcode1 ->
    forall (fcode2 : Free Shape Pos (Code Shape Pos)),
    RecPureCode fcode2 ->
    forall (fstack        : Free Shape Pos (Stack Shape Pos)),
        exec Shape Pos Cbn Partial (append Shape Pos Cbn fcode1 fcode2) fstack
        = exec Shape Pos Cbn Partial fcode2 (exec Shape Pos Cbn Partial fcode1 fstack).
  Proof.
    intros HUndefined1 HUndefined2 fcode1 HPure1 fcode2 HPure2.
    (* As we now that both pieces of code are recursively pure we, we can
       immediately destruct the monadic layer.*)
    destruct fcode1 as [ code1 | ]. 2: dependent destruction HPure1.
    destruct fcode2 as [ code2 | ]. 2: dependent destruction HPure2.
    induction code1 as [ | [ [ fn | ] | ] fcode1' IHfcode1' ] using List_ind. 4: dependent destruction HPure1.
    - (* code1 = [] *)
      (* This case is trivial. *)
      intro fstack.
      destruct fstack as [ [ | fv1 fstack1 ] | sStack pfStack ]; try reflexivity.
      simpl. f_equal. f_equal. extensionality p.
      rewrite match_stack. rewrite bind_pure.
      reflexivity.
    - (* code1 = (PUSH fn : fcode1') *)
      (* This case is easy for a pure stack but the impure case needs some extra work. *)
      intro fstack.
      dependent destruction HPure1.
      destruct fcode1' as [ code1' | ]. 2: dependent destruction HPure1.
      autoIH. specialize (IH HPure1).
      rewrite match_stack with (f := fun s => append1 _ _ _ _ _ _ >>= (fun c => exec0 _ _ _ _ c (Cons _ _ _ (pure s)))).
      rewrite match_stack with (f := fun s => exec0 _ _ _ _ _ (Cons _ _ _ (pure s))).
      (* If the stack is pure, we can apply the induction hypothesis, otherwise
         we need to destruct the second piece of code. *)
      destruct fstack as [ [ | fv1 fstack1 ] | sStack pfStack ]; try apply IH.
      destruct code2 as [ | [ [ fn2 | ] | ] fcode2' ]. 4: dependent destruction HPure2.
      + (* code2 = [] *)
        simpl. f_equal. extensionality p.
        rewrite match_stack.
        rewrite bind_pure.
        f_equal. extensionality s.
        setoid_rewrite IH. simpl.
        rewrite match_stack.
        rewrite bind_pure.
        reflexivity.
      + (* code2 = (PUSH fn2 : fcode2') *)
        simpl. f_equal. extensionality p.
        rewrite match_stack with (f := fun s => fcode2' >>= fun c => exec0 _ _ _ _ c (Cons _ _ _ (pure s))).
        rewrite bind_assoc.
        f_equal. extensionality s.
        setoid_rewrite IH. simpl.
        rewrite match_stack with (f := fun s => fcode2' >>= fun c => exec0 _ _ _ _ c (Cons _ _ _ (pure s))).
        reflexivity.
      + (* code2 = (ADD : fcode2') *)
        simpl. f_equal. extensionality p.
        rewrite bind_assoc.
        f_equal. extensionality s.
        setoid_rewrite IH. simpl.
        reflexivity.
    - (* code1 = (ADD : fcode1') *)
      (* In this case the [exec] function might return [undefined] and we need
         our two assumptions for an [undefined] [Stack]. *)
      intro fstack.
      specialize (HUndefined1 (Stack Shape Pos)).
      destruct HUndefined1 as [ sUndefined [ pfUndefined HUndefined1 ] ].
      specialize (HUndefined2 (Stack Shape Pos) _ _ HUndefined1).
      dependent destruction HPure1.
      destruct fcode1' as [ code1' | ]. 2: dependent destruction HPure1.
      autoIH. specialize (IH HPure1).
      (* As the addition reads two values from the stack, we need to destruct
         the stack. *)
      destruct fstack as [ [ | fv1 [ [ | fv2 fstack2 ] | sStack1 pfStack1 ] ] | sStack pfStack ].
      + (* fstack = pure [] *)
        (* On both sides an [undefined] is returned. *)
        simpl. rewrite HUndefined1.
        destruct code2 as [ | [ op2 | ] fcode2' ]. 3 : dependent destruction HPure2.
        * (* code2 = [] *)
          setoid_rewrite exec_strict_on_stack_arg_nil.
          f_equal. extensionality p.
          specialize (HUndefined2 p).
          destruct HUndefined2.
        * (* code2 = (op : fcode2') *)
          setoid_rewrite exec_strict_on_stack_arg_cons.
          f_equal. extensionality p.
          specialize (HUndefined2 p).
          destruct HUndefined2.
      + (* fstack = pure (fv1 : pure []) *)
        (* On both sides an [undefined] is returned. *)
        simpl. rewrite HUndefined1.
        destruct code2 as [ | [ op2 | ] fcode2' ]. 3 : dependent destruction HPure2.
        * (* code2 = [] *)
          setoid_rewrite exec_strict_on_stack_arg_nil.
          f_equal. extensionality p.
          specialize (HUndefined2 p).
          destruct HUndefined2.
        * (* code2 = (op : fcode2') *)
          setoid_rewrite exec_strict_on_stack_arg_cons.
          f_equal. extensionality p.
          specialize (HUndefined2 p).
          destruct HUndefined2.
      + (* fstack = pure (fv1 : pure (fv2 : fstack2)) *)
        (* The [exec] function can work as expected. *)
        simpl. apply IH.
      + (* fstack = pure (fv1 : impure sStack1 pfStack1) *)
        (* The execution of the first piece of code returns an impure value and
           we need to destruct the second piece of code. *)
        simpl. destruct code2 as [ | [ [ fn2 | ] | ] fcode2' ]. 4: dependent destruction HPure2.
        * (* code2 = [] *)
          simpl. f_equal. extensionality p. 
          rewrite bind_assoc.
          f_equal. extensionality s.
          rewrite match_stack.
          rewrite bind_pure.
          destruct s as [ | fv2 fstack2 ]; try reflexivity.
          setoid_rewrite IH. simpl.
          rewrite match_stack.
          rewrite bind_pure.
          reflexivity.
        * (* code2 = (PUSH fn2 : fcode2') *)
          simpl. f_equal. extensionality p. 
          rewrite bind_assoc.
          f_equal. extensionality s.
          rewrite match_stack with (f := fun s => fcode2' >>= fun c => exec0 _ _ _ _ c (Cons _ _ _ (pure s))).
          destruct s as [ | fv2 fstack2 ].
          { rewrite HUndefined1. 
            simpl. f_equal. extensionality p2.
            specialize (HUndefined2 p2).
            destruct HUndefined2. }
          setoid_rewrite IH. simpl.
          rewrite match_stack with (f := fun s => fcode2' >>= fun c => exec0 _ _ _ _ c (Cons _ _ _ (pure s))).
          reflexivity.
        * (* code2 = (ADD : fcode2')*)
          simpl. f_equal. extensionality p. 
          rewrite bind_assoc.
          f_equal. extensionality s.
          destruct s as [ | fv2 fstack2 ].
          { rewrite HUndefined1. 
            simpl. f_equal. extensionality p2.
            specialize (HUndefined2 p2).
            destruct HUndefined2. }
          setoid_rewrite IH. simpl.
          reflexivity.
      + (* fstack = impure sStack pfStack *)
        (* The execution of the first piece of code returns an impure value and
           we need to destruct the second piece of code. *)
        simpl. destruct code2 as [ | [ [ fn2 | ] | ] fcode2' ]. 4: dependent destruction HPure2.
        * (* code2 = [] *)
          simpl. f_equal. extensionality p. 
          rewrite match_stack.
          rewrite bind_pure.
          f_equal. extensionality s.
          destruct s as [  | fv1 fstack1 ]; try reflexivity.
          f_equal. extensionality s1.
          destruct s1 as [  | fv2 fstack2 ]; try reflexivity.
          setoid_rewrite IH. simpl.
          rewrite match_stack.
          rewrite bind_pure.
          reflexivity.
        * (* code2 = (PUSH fn2 : fcode2') *)
          simpl. f_equal. extensionality p.
          rewrite match_stack with (f := fun s => fcode2' >>= fun c => exec0 _ _ _ _ c (Cons _ _ _ (pure s))).
          rewrite bind_assoc.
          f_equal. extensionality s.
          destruct s as [ | fv1 fstack1 ].
          { rewrite HUndefined1. 
            simpl. f_equal. extensionality p2.
            specialize (HUndefined2 p2).
            destruct HUndefined2. }
          rewrite bind_assoc.
          f_equal. extensionality s1.
          destruct s1 as [  | fv2 fstack2 ].
          { rewrite HUndefined1. 
            simpl. f_equal. extensionality p2.
            specialize (HUndefined2 p2).
            destruct HUndefined2. }
          setoid_rewrite IH. simpl.
          rewrite match_stack with (f := fun s => fcode2' >>= fun c => exec0 _ _ _ _ c (Cons _ _ _ (pure s))).
          reflexivity.
        * (* code2 = (ADD : fcode2') *)
          simpl. f_equal. extensionality p. 
          rewrite bind_assoc.
          f_equal. extensionality s.
          destruct s as [ | fv1 fstack1 ].
          { rewrite HUndefined1. 
            simpl. f_equal. extensionality p2.
            specialize (HUndefined2 p2).
            destruct HUndefined2. }
          rewrite bind_assoc.
          f_equal. extensionality s1.
          destruct s1 as [ | fv2 fstack2 ].
          { rewrite HUndefined1. 
            simpl. f_equal. extensionality p2.
            specialize (HUndefined2 p2).
            destruct HUndefined2. }
          setoid_rewrite IH. simpl.
          reflexivity.
  Qed.

End Proofs_PureCodes.
