From Base Require Import Free Free.Instance.Maybe Prelude.
From Generated Require Import Razor.

Require Import Coq.Logic.FunctionalExtensionality.

Arguments Nil {Shape} {Pos} {A}.
Arguments Cons {Shape} {Pos} {A}.
Arguments Val {Shape} {Pos}.
Arguments Add0 {Shape} {Pos}.
Arguments PUSH {Shape} {Pos}.
Arguments ADD {Shape} {Pos}.
Arguments append {Shape} {Pos} {a}.
Arguments addInteger {Shape} {Pos}.
Arguments eval {Shape} {Pos}.
Arguments exec {Shape} {Pos}.
Arguments comp {Shape} {Pos}.
Arguments compApp {Shape} {Pos}.
Arguments comp' {Shape} {Pos}.

Create HintDb prettyDB.
Ltac pretty := autorewrite with prettyDB.
Create HintDb simplDB.
Ltac autodef := autorewrite with prettyDB simplDB; try reflexivity.

Section Rewrite_Constructors.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Lemma def_Nil :
    forall (A : Type),
        pure (@nil Shape Pos A) = Nil.
  Proof.
    reflexivity.
  Qed.

  Lemma def_Cons :
    forall (A : Type)
           (fhead : Free Shape Pos A)
           (ftail : Free Shape Pos (List Shape Pos A)),
        pure (cons fhead ftail) = Cons fhead ftail.
  Proof.
    reflexivity.
  Qed.

  Lemma def_Code_Nil :
        pure (nil : Code Shape Pos) = Nil.
  Proof.
    reflexivity.
  Qed.

  Lemma def_Code_Cons :
    forall (fhead : Free Shape Pos (Op Shape Pos))
           (ftail : Free Shape Pos (Code Shape Pos)),
        pure (cons fhead ftail) = Cons fhead ftail.
  Proof.
    reflexivity.
  Qed.

  Lemma def_Stack_Nil :
        pure (nil : Stack Shape Pos) = Nil.
  Proof.
    reflexivity.
  Qed.

  Lemma def_Stack_Cons :
    forall (fhead : Free Shape Pos (Integer Shape Pos))
           (ftail : Free Shape Pos (Stack Shape Pos)),
        pure (cons fhead ftail) = Cons fhead ftail.
  Proof.
    reflexivity.
  Qed.

  Lemma def_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos)),
        pure (val fn) = Val fn.
  Proof.
    reflexivity.
  Qed.

  Lemma def_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos)),
        pure (add0 fx fy) = Add0 fx fy.
  Proof.
    reflexivity.
  Qed.

  Lemma def_PUSH :
    forall (fn : Free Shape Pos (Integer Shape Pos)),
        pure (push fn) = PUSH fn.
  Proof.
    reflexivity.
  Qed.

  Lemma def_ADD :
        pure (@add Shape Pos) = ADD.
  Proof.
    reflexivity.
  Qed.

End Rewrite_Constructors.

Hint Rewrite def_Nil : prettyDB.
Hint Rewrite def_Cons : prettyDB.
Hint Rewrite def_Code_Nil : prettyDB.
Hint Rewrite def_Code_Cons : prettyDB.
Hint Rewrite def_Stack_Nil : prettyDB.
Hint Rewrite def_Stack_Cons : prettyDB.
Hint Rewrite def_Val : prettyDB.
Hint Rewrite def_Add : prettyDB.
Hint Rewrite def_PUSH : prettyDB.
Hint Rewrite def_ADD : prettyDB.

Section Rewrite_Maybe.

  Definition Shape := Maybe.Shape.
  Definition Pos   := Maybe.Pos.
  Definition Part  := Maybe.Partial.

  (* In this Monad the only impure value is Nothing. *)
  Lemma impure_Nothing :
    forall (A : Type) (s : Maybe.Shape) (pf : Maybe.Pos s -> Free Maybe.Shape Maybe.Pos A),
      impure s pf = Nothing.
  Proof.
    intros A s pf.
    unfold Nothing. destruct s.
    f_equal.
    extensionality p. destruct p.
  Qed.

  Lemma def_undefined_Maybe :
    forall (A : Type),
      @undefined Shape Pos Part A = Nothing.
  Proof.
    reflexivity.
  Qed.

  Lemma def_error_Maybe :
  forall (A : Type) (err : string),
    @error Shape Pos Part A err = Nothing.
  Proof.
    reflexivity.
  Qed.

End Rewrite_Maybe.

Hint Rewrite impure_Nothing : prettyDB.
Hint Rewrite def_undefined_Maybe : prettyDB.
Hint Rewrite def_error_Maybe : prettyDB.

Section Rewrite_Functions.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable Part : Partial Shape Pos.

  Lemma def_append_Nil :
    forall (A : Type)
           (fys : Free Shape Pos (List Shape Pos A)),
        append Nil fys = fys.
    Proof.
      reflexivity.
    Qed.

  Lemma def_append_Cons :
    forall (A : Type)
           (fx : Free Shape Pos A)
           (fxs fys : Free Shape Pos (List Shape Pos A)),
        append (Cons fx fxs) fys = Cons fx (append fxs fys).
    Proof.
      reflexivity.
    Qed.

  Lemma def_eval_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos)),
        eval (Val fn)
        = fn.
  Proof.
    reflexivity.
  Qed.

  Lemma def_eval_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos)),
        eval (Add0 fx fy)
        = addInteger (eval fx) (eval fy).
  Proof.
    reflexivity.
  Qed.

  Lemma def_exec_Nil :
    forall (stack : Stack Shape Pos),
        exec Part Nil (pure stack)
        = pure stack.
  Proof.
    destruct stack; reflexivity.
  Qed.

  Lemma def_exec_PUSH :
    forall (fn : Free Shape Pos (Integer Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos))
           (stack : Stack Shape Pos),
        exec Part (Cons (PUSH fn) fcode) (pure stack)
        = exec Part fcode (Cons fn (pure stack)).
  Proof.
    destruct stack; reflexivity.
  Qed.

  Lemma def_exec_ADD :
    forall (fcode : Free Shape Pos (Code Shape Pos))
           (fv1 fv2 : Free Shape Pos (Integer Shape Pos))
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec Part (Cons ADD fcode) (Cons fv1 (Cons fv2 fstack))
        = exec Part fcode (Cons (addInteger fv2 fv1) fstack).
  Proof.
    reflexivity.
  Qed.

  Lemma def_exec_ADD_0 :
    forall (fcode : Free Shape Pos (Code Shape Pos)),
        exec Part (Cons ADD fcode) Nil
        = undefined.
  Proof.
    reflexivity.
  Qed.

  Lemma def_exec_ADD_1 :
    forall (fcode : Free Shape Pos (Code Shape Pos))
           (fv1 : Free Shape Pos (Integer Shape Pos)),
        exec Part (Cons ADD fcode) (Cons fv1 Nil)
        = undefined.
  Proof.
    reflexivity.
  Qed.

  Lemma def_comp_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos)),
        comp (Val fn)
        = Cons (PUSH fn) Nil.
  Proof.
    reflexivity.
  Qed.

  Lemma def_comp_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos)),
        comp (Add0 fx fy)
        = append (append (comp fx) (comp fy)) (Cons ADD Nil).
  Proof.
    reflexivity.
  Qed.

  Lemma def_compApp_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp (Val fn) fcode
        = Cons (PUSH fn) fcode.
  Proof.
    reflexivity.
  Qed.

  Lemma def_compApp_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp (Add0 fx fy) fcode
        = compApp fx (compApp fy (Cons ADD fcode)).
  Proof.
    reflexivity.
  Qed.

  Lemma def_comp' :
    forall (fexpr : Free Shape Pos (Expr Shape Pos)),
        comp' fexpr
        = compApp fexpr Nil.
  Proof.
    reflexivity.
  Qed.

End Rewrite_Functions.

Hint Rewrite def_append_Nil : simplDB.
Hint Rewrite def_append_Cons : simplDB.
Hint Rewrite def_eval_Val : simplDB.
Hint Rewrite def_eval_Add : simplDB.
Hint Rewrite def_exec_Nil : simplDB.
Hint Rewrite def_exec_PUSH : simplDB.
Hint Rewrite def_exec_ADD : simplDB.
Hint Rewrite def_exec_ADD_0 : simplDB.
Hint Rewrite def_exec_ADD_1 : simplDB.
Hint Rewrite def_comp_Val : simplDB.
Hint Rewrite def_comp_Add : simplDB.
Hint Rewrite def_compApp_Val : simplDB.
Hint Rewrite def_compApp_Add : simplDB.
Hint Rewrite def_comp' : simplDB.

Section Rewrite_Helper_Functions.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable Part : Partial Shape Pos.

  Lemma def_append_0 :
    forall (A : Type)
           (fl1 fl2 : Free Shape Pos (List Shape Pos A)),
        append_0 Shape Pos A fl2 fl1
        = append fl1 fl2.
  Proof.
    reflexivity.
  Qed.

  Lemma def_append_1 :
    forall (A : Type)
           (l1 : List Shape Pos A)
           (fl2 : Free Shape Pos (List Shape Pos A)),
        append_1 Shape Pos A fl2 l1
        = append (pure l1) fl2.
  Proof.
    reflexivity.
  Qed.

  Lemma def_eval_0 :
    forall (expr : Expr Shape Pos),
        eval_0 Shape Pos expr
        = eval (pure expr).
  Proof.
    reflexivity.
  Qed.

  Lemma def_exec_0 :
    forall (code : Code Shape Pos)
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec_0 Shape Pos Part code fstack
        = exec Part (pure code) fstack.
  Proof.
    reflexivity.
  Qed.

  Lemma def_comp_0 :
    forall (expr : Expr Shape Pos),
        comp_0 Shape Pos expr
        = comp (pure expr).
  Proof.
    reflexivity.
  Qed.

  Lemma def_compApp_0 :
    forall (expr : Expr Shape Pos)
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp_0 Shape Pos expr fcode
        = compApp (pure expr) fcode.
  Proof.
    reflexivity.
  Qed.

End Rewrite_Helper_Functions.

Hint Rewrite def_append_1 : prettyDB.
Hint Rewrite def_append_0 : prettyDB.
Hint Rewrite def_eval_0 : prettyDB.
Hint Rewrite def_exec_0 : prettyDB.
Hint Rewrite def_comp_0 : prettyDB.
Hint Rewrite def_compApp_0 : prettyDB.
