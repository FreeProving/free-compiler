From Base Require Import Free Prelude.
From Razor.Extra Require Import ExprInd Tactic.
From Generated Require Import Razor.

Require Import Coq.Program.Equality.

(* This property states that the given expression is recursively pure.
   The integers in that expression however might still be impure. *)
Inductive RecPureExpr {Shape : Type} {Pos : Shape -> Type} : Free Shape Pos (Expr Shape Pos) -> Prop :=
  | recPureExpr_val : forall (fn : Free Shape Pos (Integer.Integer Shape Pos)),
      RecPureExpr (Val Shape Pos fn)
  | recPureExpr_add : forall (fx fy : Free Shape Pos (Expr Shape Pos)),
      RecPureExpr fx -> RecPureExpr fy -> RecPureExpr (Add0 Shape Pos fx fy).
 
 (* This property states that the for a given code the list is recursively pure
    and all contained operations are pure.
    The integers in those operations however might still be impure. *)
Inductive RecPureCode {Shape : Type} {Pos : Shape -> Type} : Free Shape Pos (Code Shape Pos) -> Prop :=
   | recPureCode_nil : RecPureCode (Nil Shape Pos)
   | recPureCode_cons : forall (op : Op Shape Pos) (fcode : Free Shape Pos (Code Shape Pos)),
       RecPureCode fcode -> RecPureCode (Cons Shape Pos (pure op) fcode).
 
Inductive RecPureStack {Shape : Type} {Pos : Shape -> Type} : Free Shape Pos (Stack Shape Pos) -> Prop :=
  | recPureStack_nil : RecPureStack (Nil Shape Pos)
  | recPureStack_cons : forall (fv : Free Shape Pos (Integer Shape Pos))
                              (fstack : Free Shape Pos (Stack Shape Pos)),
      RecPureStack fstack -> RecPureStack (Cons Shape Pos fv fstack).

Section Lemmas.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  
  (* If we apply [append] on to pieces of recursively pure code the result is recursively pure code. *)
  Lemma append_pure :
    forall (fcode1 fcode2 : Free Shape Pos (Code Shape Pos)),
    RecPureCode fcode1 ->
    RecPureCode fcode2 ->
        RecPureCode (append Shape Pos fcode1 fcode2).
  Proof.
    intros fcode1 fcode2 HPure1 HPure2.
    (* The first piece of code is pure. *)
    destruct fcode1 as [ code1 | ]. 2: dependent destruction HPure1.
    (* Do an induction over the first piece of code. *)
    induction code1 as [ | fop fcode1' ] using List_Ind.
    - simpl. apply HPure2.
    - (* The first operation in a non empty [code1] is pure. *)
      destruct fop as [ op | ]. 2: do 2 dependent destruction HPure1.
      (* The rest list in a non empty [code1] is also pure. *)
      destruct fcode1' as [ code1' | ]. 2: do 2 dependent destruction HPure1.
      simpl. apply recPureCode_cons.
      autoIH. dependent destruction HPure1. apply (IH HPure1).
  Qed.

  (* The compilation of a recursively pure expression with [comp] produces recursively pure code. *)
  Lemma comp_pure :
    forall (fexpr : Free Shape Pos (Expr Shape Pos)),
    RecPureExpr fexpr ->
        RecPureCode (comp Shape Pos fexpr).
  Proof.
    intros fexpr HPure.
    (* The given expression is pure. *)
    destruct fexpr as [ expr | sExpr pfExpr ]. 2: dependent destruction HPure.
    (* Do an induction over this expression. *)
    induction expr as [ fn | fx fy IHfx IHfy ] using Expr_Ind.
    - (* In this case, we have a single value as expression. *)
      simpl. apply recPureCode_cons. apply recPureCode_nil.
    - (* In this case, we have an addition of two expressions [fx] and [fy]. *)
      dependent destruction HPure.
      (* The expression [fx] is pure. *)
      destruct fx as [ x | sX pfX ]. 2: dependent destruction HPure1.
      (* Use the lemma [append_pure] with the three recursively pure pieces of code: 
         - (comp_0 Shape Pos x)
         - (fy >>= (fun y : Expr Shape Pos => comp_0 Shape Pos y))
         - (Cons Shape Pos (ADD Shape Pos) (Nil Shape Pos)) *)
      simpl. apply append_pure. apply append_pure.
      (* Now we need to prove that those pieces of code were indeed recursively pure. *)
      + autoIH. apply (IH HPure1).
      + (* The expression [fy] is pure. *)
        destruct fy as [ y | sY pfY ]. 2: dependent destruction HPure2.
        autoIH. apply (IH HPure2).
      + apply recPureCode_cons. apply recPureCode_nil.
    Qed.

End Lemmas.
