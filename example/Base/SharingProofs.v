(** * Proofs related to sharing. *)

From Base Require Import Free.

(* In a call-by-name setting, share does nothing. *)
Theorem cbn_no_sharing : forall (A : Type)
                                (B : Type)
                                (Shape : Type)
                                (Pos : Shape -> Type)
                                `{SA : ShareableArgs Shape Pos A}
                                (fx : Free Shape Pos A)
                                (f : Free Shape Pos A -> Free Shape Pos B),
  @share Shape Pos cbn A SA fx >>= f = f fx.
Proof. constructor. Qed.
