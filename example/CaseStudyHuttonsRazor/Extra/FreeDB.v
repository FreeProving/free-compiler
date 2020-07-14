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

(* Database for general rewriting rules to make the goal look pretty. *)
Create HintDb prettyDB.
(* Databases for using / unfolding smart constructors. *)
Create HintDb smartConstrDB.
Create HintDb invSmartConstrDB.
(* Database with function rules. *)
Create HintDb simplDB.

(* Make the goal look pretty without changing anything. *)
Ltac pretty :=
  autorewrite with prettyDB smartConstrDB.
(* Try to apply function rules and solve the goal while keeping it pretty. *)
Ltac autodef :=
  autorewrite with invSmartConstrDB;
  autorewrite with simplDB;
  pretty; try reflexivity.

(* Define rules for rewriting smart constructors. *)
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

Hint Rewrite -> def_Nil        : smartConstrDB.
Hint Rewrite <- def_Nil        : invSmartConstrDB.
Hint Rewrite -> def_Cons       : smartConstrDB.
Hint Rewrite <- def_Cons       : invSmartConstrDB.
Hint Rewrite -> def_Code_Nil   : smartConstrDB.
Hint Rewrite <- def_Code_Nil   : invSmartConstrDB.
Hint Rewrite -> def_Code_Cons  : smartConstrDB.
Hint Rewrite <- def_Code_Cons  : invSmartConstrDB.
Hint Rewrite -> def_Stack_Nil  : smartConstrDB.
Hint Rewrite <- def_Stack_Nil  : invSmartConstrDB.
Hint Rewrite -> def_Stack_Cons : smartConstrDB.
Hint Rewrite <- def_Stack_Cons : invSmartConstrDB.
Hint Rewrite -> def_Val        : smartConstrDB.
Hint Rewrite <- def_Val        : invSmartConstrDB.
Hint Rewrite -> def_Add        : smartConstrDB.
Hint Rewrite <- def_Add        : invSmartConstrDB.
Hint Rewrite -> def_PUSH       : smartConstrDB.
Hint Rewrite <- def_PUSH       : invSmartConstrDB.
Hint Rewrite -> def_ADD        : smartConstrDB.
Hint Rewrite <- def_ADD        : invSmartConstrDB.

(* Define rules for applying a function to arguments according to its definition. *)
Section Rewrite_Functions.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable Part : Partial Shape Pos.

  Lemma def_append_Nil :
    forall (A : Type)
           (fys : Free Shape Pos (List Shape Pos A)),
        append (pure nil) fys = fys.
    Proof.
      reflexivity.
    Qed.

  Lemma def_append_Cons :
    forall (A : Type)
           (fx : Free Shape Pos A)
           (fxs fys : Free Shape Pos (List Shape Pos A)),
        append (pure (cons fx fxs)) fys = pure (cons fx (append fxs fys)).
    Proof.
      reflexivity.
    Qed.

  Lemma def_eval_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos)),
        eval (pure (val fn))
        = fn.
  Proof.
    reflexivity.
  Qed.

  Lemma def_eval_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos)),
        eval (pure (add0 fx fy))
        = addInteger (eval fx) (eval fy).
  Proof.
    reflexivity.
  Qed.

  Lemma def_exec_Nil :
    forall (stack : Stack Shape Pos),
        exec Part (pure nil) (pure stack)
        = pure stack.
  Proof.
    destruct stack; reflexivity.
  Qed.

  Lemma def_exec_PUSH :
    forall (fn : Free Shape Pos (Integer Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos))
           (stack : Stack Shape Pos),
        exec Part (pure (cons (pure (push fn)) fcode)) (pure stack)
        = exec Part fcode (pure (cons fn (pure stack))).
  Proof.
    destruct stack; reflexivity.
  Qed.

  Lemma def_exec_ADD :
    forall (fcode : Free Shape Pos (Code Shape Pos))
           (fv1 fv2 : Free Shape Pos (Integer Shape Pos))
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec Part (pure (cons (pure add) fcode)) (pure (cons fv1 (pure (cons fv2 fstack))))
        = exec Part fcode (pure (cons (addInteger fv2 fv1) fstack)).
  Proof.
    reflexivity.
  Qed.

  Lemma def_exec_ADD_0 :
    forall (fcode : Free Shape Pos (Code Shape Pos)),
        exec Part (pure (cons (pure add) fcode)) (pure nil)
        = undefined.
  Proof.
    reflexivity.
  Qed.

  Lemma def_exec_ADD_1 :
    forall (fcode : Free Shape Pos (Code Shape Pos))
           (fv1 : Free Shape Pos (Integer Shape Pos)),
        exec Part (pure (cons (pure add) fcode)) (pure (cons fv1 (pure nil)))
        = undefined.
  Proof.
    reflexivity.
  Qed.

  Lemma def_comp_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos)),
        comp (pure (val fn))
        = pure (cons (pure (push fn)) (pure nil)).
  Proof.
    reflexivity.
  Qed.

  Lemma def_comp_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos)),
        comp (pure (add0 fx fy))
        = append (append (comp fx) (comp fy)) (pure (cons (pure add) (pure nil))).
  Proof.
    reflexivity.
  Qed.

  Lemma def_compApp_Val :
    forall (fn : Free Shape Pos (Integer Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp (pure (val fn)) fcode
        = pure (cons (pure (push fn)) fcode).
  Proof.
    reflexivity.
  Qed.

  Lemma def_compApp_Add :
    forall (fx fy : Free Shape Pos (Expr Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp (pure (add0 fx fy)) fcode
        = compApp fx (compApp fy (pure (cons (pure add) fcode))).
  Proof.
    reflexivity.
  Qed.

  Lemma def_comp' :
    forall (fexpr : Free Shape Pos (Expr Shape Pos)),
        comp' fexpr
        = compApp fexpr (pure nil).
  Proof.
    reflexivity.
  Qed.

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
  Proof.
    reflexivity.
  Qed.

  Lemma def_eval_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos)),
        eval (impure s pf)
        = impure s (fun p => eval (pf p)).
  Proof.
    reflexivity.
  Qed.

  Lemma def_exec_imp_Code :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Code Shape Pos))
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec Part (impure s pf) fstack
        = impure s (fun p => exec Part (pf p) fstack).
  Proof.
    reflexivity.
  Qed.

  Lemma def_exec_imp_Op :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Op Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos))
           (fstack : Free Shape Pos (Stack Shape Pos)),
        exec Part (pure (cons (impure s pf) fcode)) fstack
        = impure s (fun p => exec Part (pure (cons (pf p) fcode)) fstack).
  Proof.
    reflexivity.
  Qed.

  Lemma def_exec_Nil_imp_Stack :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Stack Shape Pos)),
        exec Part (pure nil) (impure s pf)
        = impure s (fun p => exec Part (pure nil) (pf p)).
  Proof.
    reflexivity.
  Qed.

  Lemma def_exec_Op_imp_Stack :
    forall (op : Op Shape Pos)
           (fcode : Free Shape Pos (Code Shape Pos))
           (s : Shape)
           (pf : Pos s -> Free Shape Pos (Stack Shape Pos)),
        exec Part (pure (cons (pure op) fcode)) (impure s pf)
        = impure s (fun p => exec Part (pure (cons (pure op) fcode)) (pf p)).
  Proof.
    destruct op; reflexivity.
  Qed.

  Lemma def_exec_ADD_imp_Stack1 :
    forall (fcode : Free Shape Pos (Code Shape Pos))
           (s : Shape)
           (fv1 : Free Shape Pos (Integer Shape Pos))
           (pf : Pos s -> Free Shape Pos (Stack Shape Pos)),
        exec Part (pure (cons (pure add) fcode)) (pure (cons fv1 (impure s pf)))
        = impure s (fun p => exec Part (pure (cons (pure add) fcode)) (pure (cons fv1 (pf p)))).
  Proof.
    reflexivity.
  Qed.

  Lemma def_comp_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos)),
        comp (impure s pf)
        = impure s (fun p => comp (pf p)).
  Proof.
    reflexivity.
  Qed.

  Lemma def_compApp_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos))
           (fcode : Free Shape Pos (Code Shape Pos)),
        compApp (impure s pf) fcode
        = impure s (fun p => compApp (pf p) fcode).
  Proof.
    reflexivity.
  Qed.

  Lemma def_comp'_imp_Expr :
    forall (s : Shape)
           (pf : Pos s -> Free Shape Pos (Expr Shape Pos)),
        comp' (impure s pf)
        = impure s (fun p => comp' (pf p)).
  Proof.
    reflexivity.
  Qed.

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

Hint Rewrite def_append_1  : prettyDB.
Hint Rewrite def_append_0  : prettyDB.
Hint Rewrite def_eval_0    : prettyDB.
Hint Rewrite def_exec_0    : prettyDB.
Hint Rewrite def_comp_0    : prettyDB.
Hint Rewrite def_compApp_0 : prettyDB.

(* Define specific rules for the [Maybe] monad. *)
Section Rewrite_Maybe.

  Definition Shape := Maybe.Shape.
  Definition Pos   := Maybe.Pos.
  Definition Part  := Maybe.Partial.

  (* Smart constructors. *)
  Lemma def_Just :
    forall (A : Type)
           (x : A),
        pure x = Just x.
  Proof.
    reflexivity.
  Qed.

  Lemma def_Nothing :
    forall (A : Type),
        impure tt (fun (p : Pos tt) => match p with end) = @Nothing A.
  Proof.
    reflexivity.
  Qed.

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

(* We won't use the smart constructor [Just] as it interfers with other smart constructors. *)
(* Hint Rewrite -> def_Just         : smartConstrDB. *)
Hint Rewrite <- def_Just         : invSmartConstrDB.
Hint Rewrite -> impure_Nothing   : smartConstrDB.
Hint Rewrite <- def_Nothing      : invSmartConstrDB.
Hint Rewrite def_undefined_Maybe : simplDB prettyDB.
Hint Rewrite def_error_Maybe     : simplDB prettyDB.
