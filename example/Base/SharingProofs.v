(** * Proofs related to sharing. *)

From Base Require Import Free.

(* In a call-by-name setting, share does nothing. *)
Theorem cbn_no_sharing : forall (A : Type)
                                (B : Type)
                                (Shape : Type)
                                (Pos : Shape -> Type)
                                `{I : Injectable Share.Shape Share.Pos Shape Pos}
                                `{SA : ShareableArgs Shape Pos A}
                                (fx : Free Shape Pos A)
                                (f : Free Shape Pos A -> Free Shape Pos B),
  @share Shape Pos (Cbn Shape Pos) A SA fx >>= f = f fx.
Proof. constructor. Qed.
