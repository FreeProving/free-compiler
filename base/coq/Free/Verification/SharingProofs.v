(** * Proofs related to sharing. *)

From Base Require Import Free.
From Base Require Import Free.Malias.

(* In a call-by-name setting, share does nothing. *)
Theorem cbn_no_sharing : forall (A : Type)
                                (B : Type)
                                (Shape : Type)
                                (Pos : Shape -> Type)
                                (fx : Free Shape Pos A)
                                (f : Free Shape Pos A -> Free Shape Pos B),
  @share Shape Pos (Cbn Shape Pos) A fx >>= f = f fx.
Proof. constructor. Qed.