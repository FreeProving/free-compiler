From Base Require Import Free Prelude Test.QuickCheck.
From Generated Require Import Proofs.Tracing.

Theorem trace_is_shared : quickCheck prop_trace_is_shared.
Proof.
  intros Shape Pos I S T. simpl.
  (* TODO Complete prove once [quickCheck] can is parameterized over handler. *)
Admitted.
