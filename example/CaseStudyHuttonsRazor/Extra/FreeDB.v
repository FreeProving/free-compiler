(* This file defines simplification lemmas for function definitions, a tactic
  [pretty] for 'prettifying' the goal and a tactic [autodef] as replacement
  for [simpl]. *)

From Base Require Import Free Free.Instance.Maybe Prelude.
From Generated Require Import Razor.
Import AppendAssoc.

Require Import Coq.Logic.FunctionalExtensionality.

Notation "'Nil_'" := (Nil _ _)
  (at level 9).
Notation "'Cons_' fx fxs" := (Cons _ _ fx fxs)
  (at level 10, fx, fxs at level 9).
Notation "'Val_' fn":= (Val _ _ fn)
  (at level 10, fn at level 9).
Notation "'Add0_' fx fy":= (Add0 _ _ fx fy)
  (at level 10, fx, fy at level 9).
Notation "'PUSH_' fv":= (PUSH _ _ fv)
  (at level 10, fv at level 9).
Notation "'ADD_'":= (ADD _ _)
  (at level 9).
Notation "'Just_'" := (Just _ _)
  (at level 9).
Notation "'Nothing_'" := (Nothing _ _)
  (at level 9).
Notation "'append_'" := (append _ _ cbn)
  (at level 9).
Notation "'addInteger_'" := (addInteger _ _)
  (at level 9).
Notation "'eval_'" := (eval _ _ cbn)
  (at level 9).
Notation "'exec_'" := (exec _ _ cbn)
  (at level 9).
Notation "'comp_'" := (comp _ _ cbn)
  (at level 9).
Notation "'compApp_'" := (compApp _ _ cbn)
  (at level 9).
Notation "'comp'_'" := (comp' _ _ cbn)
  (at level 9).

(* Database for general rewriting rules to make the goal look pretty. *)
Create HintDb prettyDB.
(* Database with function rules. *)
Create HintDb simplDB.

(* Make the goal look pretty without changing anything. *)
Ltac pretty :=
  autorewrite with prettyDB.
(* Try to apply function rules and solve the goal while keeping it pretty. *)
Ltac autodef :=
  autorewrite with simplDB;
  pretty; trivial.

(* Define rules for applying a function to arguments according to its definition. *)
Section Rewrite_Functions.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable S : Strategy Shape Pos.
  Variable Part : Partial Shape Pos.

  Lemma def_append_Nil :
    forall (A : Type) `{ShareableArgs Shape Pos A}
           (fys : Free Shape Pos (List Shape Pos A)),
        append_ Nil_ fys = fys.
    Proof.
      reflexivity.
    Qed.

  Lemma def_append_Cons :
    forall (A : Type) `{ShareableArgs Shape Pos A}
           (fx : Free Shape Pos A)
           (fxs fys : Free Shape Pos (List Shape Pos A)),
        append_ (Cons_ fx fxs) fys = Cons_ fx (append_ fxs fys).
    Proof.
      reflexivity.
    Qed.

  Lemma def_eval_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos)),
        eval_ (Val_ fn)
        = fn.
  Proof. trivial. Qed.

  Lemma def_eval_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos)),
        eval_ (Add0_ fx fy)
        = addInteger_ (eval_ fx) (eval_ fy).
  Proof. trivial. Qed.

  Lemma def_exec_Nil :
    forall (stack : Stack Shape Pos),
        exec_ Part Nil_ (pure stack)
        = pure stack.
  Proof.
    destruct stack; reflexivity.
  Qed.

  Lemma def_exec_PUSH :
    forall (fn : Free Shape Pos (Integer Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos))
           (stack : Stack Shape Pos),
        exec_ Part (Cons_ (PUSH_ fn) fcode) (pure stack)
        = exec_ Part fcode (Cons_ fn (pure stack)).
  Proof.
    destruct stack; reflexivity.
  Qed.

  Lemma def_exec_ADD :
    forall (fcode : Free Shape Pos (Code Shape Pos))
           (fv1 fv2 : Free Shape Pos (Integer Shape Pos))
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec_ Part (Cons_ ADD_ fcode) (Cons_ fv1 (Cons_ fv2 fstack))
        = exec_ Part fcode (Cons_ (addInteger_ fv2 fv1) fstack).
  Proof. trivial. Qed.

  Lemma def_exec_ADD_0 :
    forall (fcode : Free Shape Pos (Code Shape Pos)),
        exec_ Part (Cons_ ADD_ fcode) Nil_
        = undefined.
  Proof. trivial. Qed.

  Lemma def_exec_ADD_1 :
    forall (fcode : Free Shape Pos (Code Shape Pos))
           (fv1 : Free Shape Pos (Integer Shape Pos)),
        exec_ Part (Cons_ ADD_ fcode) (Cons_ fv1 Nil_)
        = undefined.
  Proof. trivial. Qed.

  Lemma def_comp_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos)),
        comp_ (Val_ fn)
        = Cons_ (PUSH_ fn) Nil_.
  Proof. trivial. Qed.

  Lemma def_comp_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos)),
        comp_ (Add0_ fx fy)
        = append_ (append_ (comp_ fx) (comp_ fy)) (Cons_ ADD_ Nil_).
  Proof. trivial. Qed.

  Lemma def_compApp_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp_ (Val_ fn) fcode
        = Cons_ (PUSH_ fn) fcode.
  Proof. trivial. Qed.

  Lemma def_compApp_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp_ (Add0_ fx fy) fcode
        = compApp_ fx (compApp_ fy (Cons_ ADD_ fcode)).
  Proof. trivial. Qed.

  Lemma def_comp' :
    forall (fexpr : Free Shape Pos (Expr Shape Pos)),
        comp'_ fexpr
        = compApp_ fexpr Nil_.
  Proof. trivial. Qed.

End Rewrite_Functions.

Hint Rewrite def_append_Nil  : simplDB.
Hint Rewrite def_append_Cons : simplDB.
Hint Rewrite def_eval_Val    : simplDB.
Hint Rewrite def_eval_Add    : simplDB.
Hint Rewrite def_exec_Nil    : simplDB.
Hint Rewrite def_exec_PUSH   : simplDB.
Hint Rewrite def_exec_ADD    : simplDB.
Hint Rewrite def_exec_ADD_0  : simplDB.
Hint Rewrite def_exec_ADD_1  : simplDB.
Hint Rewrite def_comp_Val    : simplDB.
Hint Rewrite def_comp_Add    : simplDB.
Hint Rewrite def_compApp_Val : simplDB.
Hint Rewrite def_compApp_Add : simplDB.
Hint Rewrite def_comp'       : simplDB.

(* Define rules for rewriting functions applied to impure arguments. *)
Section Rewrite_Functions_Impure.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable S : Strategy Shape Pos.
  Variable Part : Partial Shape Pos.

  Lemma def_append_imp_List1 :
    forall (A : Type) `{ShareableArgs Shape Pos A}
           (s : Shape)
           (pf : Pos s -> Free Shape Pos (List Shape Pos A))
           (fl2 : Free Shape Pos (List Shape Pos A)),
        append_ (impure s pf) fl2
        = impure s (fun p => append_ (pf p) fl2).
  Proof. trivial. Qed.

  Lemma def_eval_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos)),
        eval_ (impure s pf)
        = impure s (fun p => eval_ (pf p)).
  Proof. trivial. Qed.

  Lemma def_exec_imp_Code :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Code Shape Pos))
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec_ Part (impure s pf) fstack
        = impure s (fun p => exec_ Part (pf p) fstack).
  Proof. trivial. Qed.

  Lemma def_exec_imp_Op :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Op Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos))
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec_ Part (Cons_ (impure s pf) fcode) fstack
        = impure s (fun p => exec_ Part (Cons_ (pf p) fcode) fstack).
  Proof. trivial. Qed.

  Lemma def_exec_Nil_imp_Stack :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Stack Shape Pos)),
        exec_ Part Nil_ (impure s pf)
        = impure s (fun p => exec_ Part Nil_ (pf p)).
  Proof. trivial. Qed.

  Lemma def_exec_Op_imp_Stack :
    forall (op : Op Shape Pos)
           (fcode : Free Shape Pos (Code Shape Pos))
           (s : Shape)
           (pf : Pos s -> Free Shape Pos (Stack Shape Pos)),
        exec_ Part (Cons_ (pure op) fcode) (impure s pf)
        = impure s (fun p => exec_ Part (Cons_ (pure op) fcode) (pf p)).
  Proof.
    destruct op; reflexivity.
  Qed.

  Lemma def_exec_ADD_imp_Stack1 :
    forall (fcode : Free Shape Pos (Code Shape Pos))
           (s : Shape)
           (fv1 : Free Shape Pos (Integer Shape Pos))
           (pf : Pos s -> Free Shape Pos (Stack Shape Pos)),
        exec_ Part (Cons_ ADD_ fcode) (Cons_ fv1 (impure s pf))
        = impure s (fun p => exec_ Part (Cons_ ADD_ fcode) (Cons_ fv1 (pf p))).
  Proof. trivial. Qed.

  Lemma def_comp_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos)),
        comp_ (impure s pf)
        = impure s (fun p => comp_ (pf p)).
  Proof. trivial. Qed.

  Lemma def_compApp_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp_ (impure s pf) fcode
        = impure s (fun p => compApp_ (pf p) fcode).
  Proof. trivial. Qed.

  Lemma def_comp'_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos)),
        comp'_ (impure s pf)
        = impure s (fun p => comp'_ (pf p)).
  Proof. trivial. Qed.

End Rewrite_Functions_Impure.

Hint Rewrite def_append_imp_List1    : simplDB.
Hint Rewrite def_eval_imp_Expr       : simplDB.
Hint Rewrite def_exec_imp_Code       : simplDB.
Hint Rewrite def_exec_imp_Op         : simplDB.
Hint Rewrite def_exec_Nil_imp_Stack  : simplDB.
Hint Rewrite def_exec_Op_imp_Stack   : simplDB.
Hint Rewrite def_exec_ADD_imp_Stack1 : simplDB.
Hint Rewrite def_comp_imp_Expr       : simplDB.
Hint Rewrite def_compApp_imp_Expr    : simplDB.
Hint Rewrite def_comp'_imp_Expr      : simplDB.

(* Define rules for hiding helper functions. *)
Section Rewrite_Helper_Functions.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable S : Strategy Shape Pos.
  Variable Part : Partial Shape Pos.

  Lemma def_append0 :
    forall (A : Type) `{ShareableArgs Shape Pos A}
           (fl1 fl2 : Free Shape Pos (List Shape Pos A)),
        append0 Shape Pos A fl2 cbn fl1
        = append_ fl1 fl2.
  Proof. trivial. Qed.

  Lemma def_append1 :
    forall (A : Type) `{ShareableArgs Shape Pos A}
           (l1 : List Shape Pos A)
           (fl2 : Free Shape Pos (List Shape Pos A)),
        append1 Shape Pos A fl2 cbn l1
        = append_ (pure l1) fl2.
  Proof. trivial. Qed.

  Lemma def_eval0 :
    forall (expr : Expr Shape Pos),
        eval0 Shape Pos cbn expr
        = eval_ (pure expr).
  Proof. trivial. Qed.

  Lemma def_exec0 :
    forall (code : Code Shape Pos)
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec0 Shape Pos cbn Part code fstack
        = exec_ Part (pure code) fstack.
  Proof. trivial. Qed.

  Lemma def_comp0 :
    forall (expr : Expr Shape Pos),
        comp0 Shape Pos cbn expr
        = comp_ (pure expr).
  Proof. trivial. Qed.

  Lemma def_compApp0 :
    forall (expr : Expr Shape Pos)
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp0 Shape Pos cbn expr fcode
        = compApp_ (pure expr) fcode.
  Proof. trivial. Qed.

End Rewrite_Helper_Functions.

Hint Rewrite def_append1  : prettyDB.
Hint Rewrite def_append0  : prettyDB.
Hint Rewrite def_eval0    : prettyDB.
Hint Rewrite def_exec0    : prettyDB.
Hint Rewrite def_comp0    : prettyDB.
Hint Rewrite def_compApp0 : prettyDB.

(* Define specific rules for the [Maybe] monad. *)
Section Rewrite_Maybe.
  Variable Shape  : Type.
  Variable Pos    : Shape -> Type.
  Variable Inj    : Injectable Maybe.Shape Maybe.Pos Shape Pos.
  Definition Part := Maybe.Partial Shape Pos.

  (* Smart constructors. *)
  Lemma def_Just :
    forall (A : Type)
           (x : A),
        pure x = Just_ x.
  Proof. trivial. Qed.

  Lemma def_Nothing :
    forall (A : Type),
        impure (injS tt) (fun p : Pos (injS tt) =>
      match (injP p) : Void.Void with end)
      = @Nothing _ _ _ A.
  Proof. trivial. Qed.

  (* As this monad has only one impure case, we can generalize [def_Nothing]. *)
  Lemma impure_Nothing :
    forall (A : Type)
           (s : Maybe.Shape)
           (pf : Maybe.Pos s -> Free Maybe.Shape Maybe.Pos A),
        impure s pf = Nothing_.
  Proof.
    intros A s pf.
    unfold Nothing. destruct s.
    f_equal.
    extensionality p. destruct p.
  Qed.

  (* Partial instance. *)
  Lemma def_undefined_Maybe :
    forall (A : Type),
      @undefined Shape Pos Part A = Nothing_.
  Proof. trivial. Qed.

  Lemma def_error_Maybe :
    forall (A : Type)
           (err : string),
    @error Shape Pos Part A err = Nothing_.
  Proof. trivial. Qed.

End Rewrite_Maybe.

(* We won't use the smart constructor [Just] as it interferes with other smart constructors. *)
(* Hint Rewrite -> def_Just         : smartConstrDB. *)
Hint Rewrite <- def_Just         : simplDB.
Hint Rewrite -> impure_Nothing   : prettyDB.
Hint Rewrite <- def_Nothing      : simplDB.
Hint Rewrite def_undefined_Maybe : simplDB prettyDB.
Hint Rewrite def_error_Maybe     : simplDB prettyDB.
