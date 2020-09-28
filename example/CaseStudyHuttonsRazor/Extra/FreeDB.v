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
Arguments Just {Shape'} {Pos'} {H} {A}.
Arguments Nothing {Shape'} {Pos'} {H} {A}.
Arguments append {Shape} {Pos} {a}.
Arguments addInteger {Shape} {Pos}.
Arguments eval {Shape} {Pos}.
Arguments exec {Shape} {Pos}.
Arguments comp {Shape} {Pos}.
Arguments compApp {Shape} {Pos}.
Arguments comp' {Shape} {Pos}.

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
  Variable Part : Partial Shape Pos.

  Lemma def_append_Nil :
    forall (A : Type)
           (fys : Free Shape Pos (List Shape Pos A)),
        append Nil_ fys = fys.
    Proof.
      reflexivity.
    Qed.

  Lemma def_append_Cons :
    forall (A : Type)
           (fx : Free Shape Pos A)
           (fxs fys : Free Shape Pos (List Shape Pos A)),
        append (Cons_ fx fxs) fys = Cons_ fx (append fxs fys).
    Proof.
      reflexivity.
    Qed.

  Lemma def_eval_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos)),
        eval (Val_ fn)
        = fn.
  Proof. trivial. Qed.

  Lemma def_eval_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos)),
        eval (Add0_ fx fy)
        = addInteger (eval fx) (eval fy).
  Proof. trivial. Qed.

  Lemma def_exec_Nil :
    forall (stack : Stack Shape Pos),
        exec Part Nil_ (pure stack)
        = pure stack.
  Proof.
    destruct stack; reflexivity.
  Qed.

  Lemma def_exec_PUSH :
    forall (fn : Free Shape Pos (Integer Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos))
           (stack : Stack Shape Pos),
        exec Part (Cons_ (PUSH_ fn) fcode) (pure stack)
        = exec Part fcode (Cons_ fn (pure stack)).
  Proof.
    destruct stack; reflexivity.
  Qed.

  Lemma def_exec_ADD :
    forall (fcode : Free Shape Pos (Code Shape Pos))
           (fv1 fv2 : Free Shape Pos (Integer Shape Pos))
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec Part (Cons_ ADD_ fcode) (Cons_ fv1 (Cons_ fv2 fstack))
        = exec Part fcode (Cons_ (addInteger fv2 fv1) fstack).
  Proof. trivial. Qed.

  Lemma def_exec_ADD_0 :
    forall (fcode : Free Shape Pos (Code Shape Pos)),
        exec Part (Cons_ ADD_ fcode) Nil_
        = undefined.
  Proof. trivial. Qed.

  Lemma def_exec_ADD_1 :
    forall (fcode : Free Shape Pos (Code Shape Pos))
           (fv1 : Free Shape Pos (Integer Shape Pos)),
        exec Part (Cons_ ADD_ fcode) (Cons_ fv1 Nil_)
        = undefined.
  Proof. trivial. Qed.

  Lemma def_comp_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos)),
        comp (Val_ fn)
        = Cons_ (PUSH_ fn) Nil_.
  Proof. trivial. Qed.

  Lemma def_comp_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos)),
        comp (Add0_ fx fy)
        = append (append (comp fx) (comp fy)) (Cons_ ADD_ Nil_).
  Proof. trivial. Qed.

  Lemma def_compApp_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp (Val_ fn) fcode
        = Cons_ (PUSH_ fn) fcode.
  Proof. trivial. Qed.

  Lemma def_compApp_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp (Add0_ fx fy) fcode
        = compApp fx (compApp fy (Cons_ ADD_ fcode)).
  Proof. trivial. Qed.

  Lemma def_comp' :
    forall (fexpr : Free Shape Pos (Expr Shape Pos)),
        comp' fexpr
        = compApp fexpr Nil_.
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
  Variable Part : Partial Shape Pos.

  Lemma def_append_imp_List1 :
    forall (A : Type)
           (s : Shape)
           (pf : Pos s -> Free Shape Pos (List Shape Pos A))
           (fl2 : Free Shape Pos (List Shape Pos A)),
        append (impure s pf) fl2
        = impure s (fun p => append (pf p) fl2).
  Proof. trivial. Qed.

  Lemma def_eval_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos)),
        eval (impure s pf)
        = impure s (fun p => eval (pf p)).
  Proof. trivial. Qed.

  Lemma def_exec_imp_Code :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Code Shape Pos))
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec Part (impure s pf) fstack
        = impure s (fun p => exec Part (pf p) fstack).
  Proof. trivial. Qed.

  Lemma def_exec_imp_Op :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Op Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos))
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec Part (Cons_ (impure s pf) fcode) fstack
        = impure s (fun p => exec Part (Cons_ (pf p) fcode) fstack).
  Proof. trivial. Qed.

  Lemma def_exec_Nil_imp_Stack :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Stack Shape Pos)),
        exec Part Nil_ (impure s pf)
        = impure s (fun p => exec Part Nil_ (pf p)).
  Proof. trivial. Qed.

  Lemma def_exec_Op_imp_Stack :
    forall (op : Op Shape Pos)
           (fcode : Free Shape Pos (Code Shape Pos))
           (s : Shape)
           (pf : Pos s -> Free Shape Pos (Stack Shape Pos)),
        exec Part (Cons_ (pure op) fcode) (impure s pf)
        = impure s (fun p => exec Part (Cons_ (pure op) fcode) (pf p)).
  Proof.
    destruct op; reflexivity.
  Qed.

  Lemma def_exec_ADD_imp_Stack1 :
    forall (fcode : Free Shape Pos (Code Shape Pos))
           (s : Shape)
           (fv1 : Free Shape Pos (Integer Shape Pos))
           (pf : Pos s -> Free Shape Pos (Stack Shape Pos)),
        exec Part (Cons_ ADD_ fcode) (Cons_ fv1 (impure s pf))
        = impure s (fun p => exec Part (Cons_ ADD_ fcode) (Cons_ fv1 (pf p))).
  Proof. trivial. Qed.

  Lemma def_comp_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos)),
        comp (impure s pf)
        = impure s (fun p => comp (pf p)).
  Proof. trivial. Qed.

  Lemma def_compApp_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp (impure s pf) fcode
        = impure s (fun p => compApp (pf p) fcode).
  Proof. trivial. Qed.

  Lemma def_comp'_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos)),
        comp' (impure s pf)
        = impure s (fun p => comp' (pf p)).
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
  Variable Part : Partial Shape Pos.

  Lemma def_append0 :
    forall (A : Type)
           (fl1 fl2 : Free Shape Pos (List Shape Pos A)),
        append0 Shape Pos A fl2 fl1
        = append fl1 fl2.
  Proof. trivial. Qed.

  Lemma def_append1 :
    forall (A : Type)
           (l1 : List Shape Pos A)
           (fl2 : Free Shape Pos (List Shape Pos A)),
        append1 Shape Pos A fl2 l1
        = append (pure l1) fl2.
  Proof. trivial. Qed.

  Lemma def_eval0 :
    forall (expr : Expr Shape Pos),
        eval0 Shape Pos expr
        = eval (pure expr).
  Proof. trivial. Qed.

  Lemma def_exec0 :
    forall (code : Code Shape Pos)
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec0 Shape Pos Part code fstack
        = exec Part (pure code) fstack.
  Proof. trivial. Qed.

  Lemma def_comp0 :
    forall (expr : Expr Shape Pos),
        comp0 Shape Pos expr
        = comp (pure expr).
  Proof. trivial. Qed.

  Lemma def_compApp0 :
    forall (expr : Expr Shape Pos)
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp0 Shape Pos expr fcode
        = compApp (pure expr) fcode.
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
        pure x = Just x.
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
        impure s pf = Nothing.
  Proof.
    intros A s pf.
    unfold Nothing. destruct s.
    f_equal.
    extensionality p. destruct p.
  Qed.

  (* Partial instance. *)
  Lemma def_undefined_Maybe :
    forall (A : Type),
      @undefined Shape Pos Part A = Nothing.
  Proof. trivial. Qed.

  Lemma def_error_Maybe :
    forall (A : Type)
           (err : string),
    @error Shape Pos Part A err = Nothing.
  Proof. trivial. Qed.

End Rewrite_Maybe.

(* We won't use the smart constructor [Just] as it interferes with other smart constructors. *)
(* Hint Rewrite -> def_Just         : smartConstrDB. *)
Hint Rewrite <- def_Just         : simplDB.
Hint Rewrite -> impure_Nothing   : prettyDB.
Hint Rewrite <- def_Nothing      : simplDB.
Hint Rewrite def_undefined_Maybe : simplDB prettyDB.
Hint Rewrite def_error_Maybe     : simplDB prettyDB.
