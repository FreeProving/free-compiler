(** Operators that model call-by-value, call-by-name and call-by-need 
   evaluation. *)

From Base Require Import Free.
From Base Require Export Free.Instance.Comb.
From Base Require Export Free.Instance.Share.

(* An operator to model call-by-value evaluation *)
Definition cbv {A : Type} {Shape : Type} {Pos : Shape -> Type} (p : Free Shape Pos A) 
  : Free Shape Pos (Free Shape Pos A) :=
  p >>= fun x => pure (pure x).

(* An operator to model call-by-name evaluation *)
Definition cbn {A : Type} {Shape : Type} {Pos : Shape -> Type}
  (p : Free Shape Pos A) 
  : Free Shape Pos (Free Shape Pos A) := 
  pure p.

(* An operator to model call-by-need evaluation *)
Definition cbneed {A : Type} {Shape : Type} {Pos : Shape -> Type}
  `{Injectable Share.Shape Share.Pos Shape Pos} (p : Free Shape Pos A)
  : Free Shape Pos (Free Shape Pos A) :=
  Get _ _ >>= fun '(i,j) =>
  Put _ _ (i+1,j) >>
  pure (BeginShare _ _ (i,j) >>
      Put _ _ (i,j+1) >>
      p >>= fun x =>
      Put _ _ (i+1,j) >>
      EndShare _ _ (i,j) >>
      pure x).

Instance Cbneed (Shape : Type) (Pos : Shape -> Type)
                `{I : Injectable Share.Shape Share.Pos Shape Pos}
 : Shareable Shape Pos | 1 := {
    share A p := @cbneed A Shape Pos I p
}.
Instance Cbn (Shape : Type) (Pos : Shape -> Type)
 : Shareable Shape Pos | 2 := {
    share A p := @cbn A Shape Pos p
}.