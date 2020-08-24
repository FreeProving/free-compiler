(** Operators that model call-by-value, call-by-name and call-by-need 
   evaluation. *)

From Base Require Import Free.
From Base Require Export Free.Instance.Comb.
From Base Require Export Free.Instance.Share.

(* An operator to model call-by-value evaluation *)
Definition cbv {A : Type} (Shape : Type) (Pos : Shape -> Type) (p : Free Shape Pos A) 
  : Free Shape Pos (Free Shape Pos A) :=
  p >>= fun x => pure (pure x).

(* An operator to model call-by-name evaluation *)
Definition cbn {A : Type} (Shape : Type) (Pos : Shape -> Type)
  (p : Free Shape Pos A) 
  : Free Shape Pos (Free Shape Pos A) := 
  pure p.

Section SecCbneed.

Variable Shape : Type.
Variable Pos : Shape -> Type.

Notation "'Get''" := (Get Shape Pos).
Notation "'Put''" := (Put Shape Pos).
Notation "'BeginShare''" := (BeginShare Shape Pos).
Notation "'EndShare''" := (EndShare Shape Pos).

Definition cbneed {A : Type}
                  `{Injectable Share.Shape Share.Pos Shape Pos}
                  `{ShareableArgs Shape Pos A}
                  (p : Free Shape Pos A)
  : Free Shape Pos (Free Shape Pos A) :=
  Get' >>= fun '(i,j) =>
  Put' (i+1,j) >>
  pure (BeginShare' (i,j) >>
      Put' (i,j+1) >>
      p >>= fun x =>
      shareArgs x >>= fun x' =>
      Put' (i+1,j) >>
      EndShare' (i,j) >>
      pure x').

End SecCbneed.

(* Shareable instances. *)
Instance Cbneed (Shape : Type) (Pos : Shape -> Type)
                `{I : Injectable Share.Shape Share.Pos Shape Pos}
 : Shareable Shape Pos | 1 := {
    share A S p := @cbneed Shape Pos A I S p
}.

(* The Share effect is not actually needed, but we need to
   ensure it is there so cbn is compatible with share. *)
Instance Cbn (Shape : Type) (Pos : Shape -> Type) 
             `{Injectable Share.Shape Share.Pos Shape Pos}
 : Shareable Shape Pos | 2 := {
    share A S p := @cbn A Shape Pos p
}.
